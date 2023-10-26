# CHANGELOG 

Changes from ApogeoRV v1.0.0:

## ApogeoRV v1.0.1

- Deleted ROB Snapshot Register (22 / 10 / 2023)
    * Shortened the critical path on bypass stage
    * Decreased LUT usage from 8711 to 8446 in the board configuration (Post-Synthesis)
    * Decreased LUT usage from 8512 to 8021 in the board configuration (Post-Implementation)
- Removed pipeline registers before commit stage, snapshot registers constitute the real stage register now. Reduced logic on bypass and on buffer manager FSM (24 / 10 / 2023)
    * Shortened the critical path on bypass stage
    * Decreased LUT usage from 8446 to 7967 in the board configuration (Post-Synthesis)
    * Decreased LUT usage from 8021 to 7597 in the board configuration (Post-Implementation)