proc simulate {file_name} {
    set project_file "/home/gabbed/Vivado/Projects/RV32-Apogeo/RV32-Apogeo.xpr"
    open_project $project_file
    launch_simulation
    create_waveform
    run_simulation
    close_waveform
    close_project
    exit
}
simulate $argv