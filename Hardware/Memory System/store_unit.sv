`ifndef STORE_UNIT_SV   
    `define STORE_UNIT_SV

//TODO: 31 bit data

`include "../Include/memory_system_pkg.sv"
`include "../Include/rv32_instructions_pkg.sv"
`include "../Include/configuration_pkg.sv"

module store_unit (
    input  logic             clk_i,
    input  logic             clk_en_i,
    input  logic             rst_n_i,
    input  logic [63:0]      data_store_i,
    input  data_cache_addr_t addr_store_i,
    input  logic             valid_addr_i,
    input  logic             cache_hit_i,
    input  logic             cache_miss_i,
    input  logic             mem_unit_ackn_i,
    input  mem_op_width_t    operation_width_i,
    input  instr_packet_t    instr_packet_i,

    output logic             illegal_region_access_o,
    output logic             illegal_word_alignment_o,
    output logic             cache_write_o,
    output logic             store_buffer_write_o,
    output logic             cache_line_status_read_o,
    output logic [3:0]       cache_byte_write_o,
    output logic [31:0]      data_store_o,
    output data_cache_addr_t addr_store_o,
    output logic             idle_o,
    output logic             valid_o,
    output instr_packet_t    instr_packet_o
);

    `define BETWEEN(low, high) low <= addr_store_i & addr_store_i <= high


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [1:0] {IDLE, DATA, DELAY, MEMORY} fsm_state_t;

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (clk_en_i) begin
                state_CRT <= state_NXT;
            end
        end : state_register


    logic [63:0]   data_store_CRT, data_store_NXT;
    logic [31:0]   store_address_CRT, store_address_NXT;
    logic          bufferable_CRT, bufferable_NXT;
    logic          cachable_CRT, cachable_NXT;
    logic          double_word_CRT, double_word_NXT;
    instr_packet_t ipacket_CRT, ipacket_NXT;
    mem_op_width_t operation_width_CRT, operation_width_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : datapath_register
            if (!rst_n_i) begin
                data_store_CRT <= 64'b0;
                store_address_CRT <= 32'hFFFF_FFFF;
                bufferable_CRT <= 1'b1;
                cachable_CRT <= 1'b1;
                ipacket_CRT <= 'b0;
            end else if (clk_en_i) begin
                data_store_CRT <= data_store_NXT;
                store_address_CRT <= store_address_NXT;
                bufferable_CRT <= bufferable_NXT;
                cachable_CRT <= cachable_NXT;
                ipacket_CRT <= ipacket_NXT;
            end
        end : datapath_register


        always_comb begin : fsm_logic
            /* Default values */
            operation_width_NXT = operation_width_CRT;
            store_address_NXT = store_address_CRT;
            double_word_NXT = double_word_CRT;
            data_store_NXT = data_store_CRT;
            state_NXT = state_CRT;

            cache_line_status_read_o = 1'b0;
            cache_byte_write_o = 8'b0;
            cache_write_o = 1'b0;
            valid_o = 1'b0;

            case (state_CRT) 
                
                /*
                 *  Wait until the address is valid then send a read operation
                 *  to cache. In parallel, address is constantly checked for
                 *  exceptions and microinstructions generation
                 */
                IDLE: begin 
                    if (valid_addr_i) begin
                        if (cachable_NXT) begin 
                            state_NXT = DATA;
                        end else begin 
                            state_NXT = MEMORY;
                        end

                        /* Read only status bits (tag, valid, dirty) */
                        cache_line_status_read_o = 1'b1;
                    end

                    data_store_NXT = data_store_i;
                    store_address_NXT = addr_store_i;
                    operation_width_NXT = operation_width_i;
                    double_word_NXT = 1'b0;
                end
                
                /* 
                 *  Data arrives 1 clock cycle after address is supplied, data gets 
                 *  modified based on the type of operations. The read result however
                 *  can be an hit or a miss, if miss then the data needs to be stored
                 *  into the store buffer or sended directly to memory unit, else the
                 *  data can be stored into cache 
                 */
                DATA: begin
                    if (cache_hit_i) begin 
                        state_NXT = DELAY;
                        cache_write_o = 1'b1;
                    end else if (cache_miss_i) begin
                        state_NXT = MEMORY;
                    end

                    case (operation_width_CRT)
                        BYTE: begin
                            case (store_address_CRT[1:0])
                                2'b00: begin 
                                    data_store_NXT[7:0] = data_store_CRT[7:0];
                                    cache_byte_write_o = 8'b0000_0001;
                                end

                                2'b01: begin 
                                    data_store_NXT[15:8] = data_store_CRT[7:0];
                                    cache_byte_write_o = 8'b0000_0010;
                                end                                    

                                2'b10: begin
                                    data_store_NXT[23:16] = data_store_CRT[7:0]; 
                                    cache_byte_write_o = 8'b0000_0100;
                                end

                                2'b11: begin
                                    data_store_NXT[31:24] = data_store_CRT[7:0]; 
                                    cache_byte_write_o = 8'b0000_1000;
                                end
                            endcase
                        end

                        HALF_WORD: begin
                            if (!store_address_CRT[0]) begin
                                data_store_NXT[15:0] = data_store_CRT[15:0];
                                cache_byte_write_o = 8'b0000_0011;
                            end else begin
                                data_store_NXT[31:16] = data_store_CRT[15:0];
                                cache_byte_write_o = 8'b0000_1100; 
                            end
                        end

                        WORD: begin
                            cache_byte_write_o = 8'b0000_1111;
                        end 
                        
                        DOUBLE_WORD: begin 
                            cache_byte_write_o = 8'b1111_1111;
                        end
                    endcase
                end

                /* 
                 *  During this state, the data is stable and can be safely written 
                 *  into the cache.
                 */
                DELAY: begin
                    state_NXT = IDLE;
                end

                /*
                 *  Data get stored into the write buffer to let the CPU execute other
                 *  instructions or get sended to the main memory directly if not bufferable 
                 */
                MEMORY: begin
                    if (bufferable_CRT) begin
                        store_buffer_write_o = 1'b1;
                        state_NXT = IDLE;
                        valid_o = 1'b1;
                    end else begin
                        state_NXT = mem_unit_ackn_i ? IDLE : MEMORY;
                        valid_o = mem_unit_ackn_i;
                    end
                end
            endcase
        end : fsm_logic

    
    assign idle_o = (state_NXT == IDLE);

    assign instr_packet_o = ipacket_CRT;

    assign addr_store_o = store_address_CRT;
    assign data_store_o = data_store_CRT;


//-----------------//
//  ADDRESS CHECK  //
//-----------------//

    logic between_boot_region;
    assign between_boot_region = `BETWEEN(BOOT_REGION_START, BOOT_REGION_END);

    logic between_int_table_region;
    assign between_int_table_region = `BETWEEN(INTERRUPT_TABLE_REGION_START, INTERRUPT_TABLE_REGION_END);

    logic between_ext_nvm_region;
    assign between_ext_nvm_region = `BETWEEN(EXT_NVM_REGION_START, EXT_NVM_REGION_END);

    logic between_int_nvm_region;
    assign between_int_nvm_region = `BETWEEN(INT_NVM_REGION_START, INT_NVM_REGION_END);

    logic between_perf_cnt_region;
    assign between_perf_cnt_region = `BETWEEN(PERF_CNT_REGION_START, PERF_CNT_REGION_END);

    logic between_IO_region;
    assign between_IO_region = `BETWEEN(IO_REGION_START, IO_REGION_END);


        /* Check if address is aligned to words byte number */
        always_comb begin : alignment_check
            /* Default value */
            illegal_word_alignment_o = 1'b0;
            illegal_region_access_o = 1'b0;
            ipacket_NXT = ipacket_CRT;
            cachable_NXT = cachable_CRT;
            bufferable_NXT = bufferable_CRT;

            if (valid_addr_i) begin 
                case (operation_width_i)
                    BYTE: illegal_word_alignment_o = 1'b0;

                    HALF_WORD: illegal_word_alignment_o = addr_store_i[0];

                    WORD: illegal_word_alignment_o = |addr_store_i[1:0];

                    DOUBLE_WORD: illegal_word_alignment_o = |addr_store_i[2:0];
                endcase

                ipacket_NXT = instr_packet_i;

                /* Writing to boot region is illegal */
                if (between_boot_region) begin
                    illegal_region_access_o = 1'b1;
                    ipacket_NXT.exception = 1'b1;
                    ipacket_NXT.exception_vector = ILLEGAL_MEMORY_ACCESS;
                end

                /* Data cannot be inserted into the write buffer and needs to get to main memory 
                 * as soon as possible */
                if (between_int_table_region | between_perf_cnt_region | between_IO_region) begin
                    bufferable_NXT = 1'b0;
                end

                /* Data cannot be cached because it may be written by other devices while in cache
                 * so the value is not valid */
                if (between_perf_cnt_region | between_IO_region) begin
                    cachable_NXT = 1'b0;
                end
            end
        end : alignment_check

endmodule : store_unit

`endif 