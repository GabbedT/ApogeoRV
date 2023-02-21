`ifndef DATA_CACHE_INTERFACE_SV
    `define DATA_CACHE_INTERFACE_SV

`include "../Packages/Execution Unit/load_store_unit_pkg.sv"
`include "../Packages/apogeo_pkg.sv"
`include "../Headers/apogeo_configuration.svh"

interface data_cache_interface;

    /* 
     * External interface (Load Unit) 
     */

    /* External data loaded and valid bit */
    data_word_t loaded_data;
    logic data_valid;

    /* One hot signal of the word number supplied 
     * during cache allocation */
    logic [BLOCK_WORDS - 1:0] word_select;

    /* Memory load address */
    full_address_t load_address;

    /* Load request */
    logic load_request;

    modport load_memory_master (
        input loaded_data,
        input data_valid,
        input word_select,
        
        output load_address,
        output load_request
    );


    /* 
     * External interface (Store Unit) 
     */

    /* Invalidate request and address */
    logic invalidate_request;
    data_cache_address_t invalidate_address;

    /* Store done */
    logic data_stored;

    /* Data to store, store address and request */
    data_word_t store_data; 
    full_address_t store_address;
    store_width_t store_width;

    logic store_request;

    /* Invalidate request acknowledge */
    logic acknowledge_request;

    modport store_memory_master (
        input invalidate_request,
        input invalidate_address,
        input data_stored,

        output store_data,
        output store_address,
        output store_width,
        output store_request,
        output acknowledge_request
    );


    /* 
     * Store buffer interface 
     */

    /* Load address match in buffer and 
     * data fowarded */
    logic address_match;
    data_word_t fowarded_data;

    /* Buffer status */
    logic full;

    /* Port access granted */
    logic ldu_port_granted;
    logic stu_port_granted;

    /* Data to push */
    store_buffer_entry_t ldu_packet;
    store_buffer_entry_t stu_packet; 

    /* Push request */
    logic ldu_push_request;                   
    logic stu_push_request;

    modport store_buffer_master (
        input address_match,
        input fowarded_data,
        input full,
        input ldu_port_granted,
        input stu_port_granted,

        output ldu_packet,
        output stu_packet,
        output ldu_push_request,
        output stu_push_request
    );

    modport stbuf_stu_master (
        input stu_port_granted,
        input full,

        output stu_packet,
        output stu_push_request
    );

    modport stbuf_stu_slave (
        output stu_packet,
        output stu_push_request,

        input stu_port_granted,
        input full

    );


    /* 
     * Store unit interface 
     */

    /* Data can be pushed into the buffer */
    logic data_bufferable;

    /* Cache store request */
    logic store_cache_request;

    /* Cache store data, address and width */
    data_word_t store_data_cache;
    full_address_t store_address_cache;
    store_width_t store_width_cache;

    /* Store unit idle */
    logic stu_idle;

    /* Controller idle */
    logic stctrl_idle;

    /* Operation done */
    logic data_cache_stored;

    modport store_unit_slave (
        input data_bufferable,
        input store_cache_request,
        input store_data_cache,
        input store_address_cache,
        input store_width_cache,
        input stu_idle,

        output stctrl_idle,
        output data_cache_stored
    );

    modport store_unit_master (
        input stctrl_idle,
        input data_cache_stored,

        output data_bufferable,
        output store_cache_request,
        output store_data_cache,
        output store_address_cache,
        output store_width_cache,
        output stu_idle
    );


    /* 
     * Load unit interface 
     */

    /* Load request and address */
    logic load_cache_request;

    /* Data loaded valid */
    logic data_valid_cache;

    /* Data and address load */
    full_address_t load_cache_address;
    data_word_t loaded_cache_data;

    /* Operation done */
    logic ldctrl_done;

    modport load_unit_slave (
        input load_cache_request,
        input load_cache_address,

        output loaded_cache_data,
        output data_valid_cache,
        output ldctrl_done
    );

    modport load_unit_master (
        input loaded_cache_data,
        input data_valid_cache,
        input ldctrl_done,
        
        output load_cache_request,
        output load_cache_address
    );

endinterface : data_cache_interface

`endif 