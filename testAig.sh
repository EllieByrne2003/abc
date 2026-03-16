#!/bin/bash

# Check command line arguments
if [ $# -ne 2 ]; then
    echo "Usage: $0 <circuit_file> <custom_commands>"
    echo "  custom_commands : semicolon-separated list of ABC commands, e.g., 'resyn2; dc2; print_stats'"
    exit 1
fi

circuit="$1"
custom_cmds="$2"

# Verify that the circuit file exists
if [ ! -f "$circuit" ]; then
    echo "Error: Circuit file '$circuit' not found."
    exit 1
fi

# Check if abc is in PATH
if ! command -v ./abc &> /dev/null; then
    echo "Error: abc not found in PATH. Please ensure ABC is installed and accessible."
    exit 1
fi

# ----------------------------------------------------------------------
# Define standard built-in synthesis scripts (commands) in ABC
# Modify this list according to your ABC version or needs.
# ----------------------------------------------------------------------
standard_scripts=(
    "resyn"
    "resyn2"
    "resyn2a"
    "resyn3"
    "compress"
    "compress2"
    "choice"
    "choice2"
    "rwsat"
    "drwsat2"
    "share"
    "addinit"
    "blif2aig"
    "v2p"
    "g2p"
    "&sw_"
    "&fx_"
    "&dc3"
    "&dc4"
)

iwls_scripts=(
    "src_rw"
    "src_rs"
    "src_rws"
    "resyn2rs"
    "r2rs"
    "compress2rs"
    "c2rs"
    "&resyn2rs"
    "&compress2rs"
)

# Output file: <circuit>_results.txt
outfile="${circuit}_AIG_results.txt"

# Clear (or create) the output file
> "$outfile"

# Function to run a command string and append its output to the result file
run_and_append() {
    local label="$1"
    local cmd_string="$2"

    echo "================================================================================" >> "$outfile"
    echo "=== $label ===" >> "$outfile"
    echo "================================================================================" >> "$outfile"

    # Run abc with the given commands; capture both stdout and stderr
    ./abc -c "read $circuit; $cmd_string" 2>&1 | sed $'s/\x1b\[[0-9;]*m//g' >> "$outfile"

    # Add a blank line for readability
    echo >> "$outfile"
}

# ----------------------------------------------------------------------
# Run each standard script + print_stats
# ----------------------------------------------------------------------
for script in "${standard_scripts[@]}"; do
    run_and_append "Standard script: $script (with print_stats)" "$script; strash; print_stats"
done

# ----------------------------------------------------------------------
# Run each iwls script + print_stats
# ----------------------------------------------------------------------
for script in "${iwls_scripts[@]}"; do
    run_and_append "IWLS script: $script (with print_stats)" "$script; strash; print_stats"
done

# ----------------------------------------------------------------------
# Run lazy mans synthesis
# ----------------------------------------------------------------------
run_and_append "Lazy mans synthesis: recadd3 (with print_stats)" "rec_start3; recadd3; strash; print_stats"

# ----------------------------------------------------------------------
# Run the user-provided custom script (as given)
# ----------------------------------------------------------------------
run_and_append "Custom script: $custom_cmds" "$custom_cmds; strash; print_stats"

echo "All runs completed. Results written to: $outfile"