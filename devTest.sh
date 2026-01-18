#!/bin/bash

set -e

# compare_abc.sh - Compare ABC outputs between old and new versions, ignoring timestamps

# Configuration
INPUT_FILE="i10.aig"
OLD_OUTPUT="i10-old.v"
NEW_OUTPUT="i10-new.v"
OLD_LOG="oldabc_output.txt"
NEW_LOG="newabc_output.txt"

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

print_error() { echo -e "${RED}Error: $1${NC}"; }
print_success() { echo -e "${GREEN}$1${NC}"; }
print_warning() { echo -e "${YELLOW}Warning: $1${NC}"; }

# Check if command was provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <abc_command>"
    echo ""
    echo "Examples:"
    echo "  $0 'balance; rewrite'"
    echo "  $0 'renode -b'"
    echo "  $0 'logic; sop; fx'"
    exit 1
fi

abc_command="$*"
echo "Testing command: $abc_command"

# Check for required files
check_required_files() {
    local missing_files=()
    
    [ ! -f "./oldabc" ] && missing_files+=("oldabc")
    [ ! -f "makefile" ] && [ ! -f "Makefile" ] && missing_files+=("Makefile")
    [ ! -f "$INPUT_FILE" ] && missing_files+=("$INPUT_FILE")
    
    if [ ${#missing_files[@]} -gt 0 ]; then
        print_error "Missing required files: ${missing_files[*]}"
        exit 1
    fi
}

check_required_files

# Build new version
echo "Building new ABC version..."
if ! make; then
    print_error "Build failed!"
    exit 1
fi

if [ ! -f "./abc" ]; then
    print_error "abc executable not found after build!"
    exit 1
fi

chmod +x ./oldabc ./abc 2>/dev/null

# Run oldabc
echo "Running oldabc..."
if ! ./oldabc -c "read $INPUT_FILE; $abc_command; write $OLD_OUTPUT" > "$OLD_LOG" 2>&1; then
    print_warning "oldabc exited with error (check $OLD_LOG)"
fi
old_exit_code=$?

# Run new abc
echo "Running new abc..."
if ! ./abc -c "read $INPUT_FILE; $abc_command; write $NEW_OUTPUT" > "$NEW_LOG" 2>&1; then
    print_warning "new abc exited with error (check $NEW_LOG)"
fi
new_exit_code=$?

# Function to compare files while ignoring timestamp differences
compare_files_ignore_timestamp() {
    local file1="$1"
    local file2="$2"
    local description="$3"
    
    echo -e "\n=== Comparing $description (ignoring timestamps) ==="
    
    if [ ! -f "$file1" ] || [ ! -f "$file2" ]; then
        print_error "Missing one or both $description files"
        return 2
    fi
    
    # Create versions with timestamps stripped for comparison
    local temp1=$(mktemp)
    local temp2=$(mktemp)
    
    # Strip timestamp lines (lines containing "written by ABC on")
    # This handles both formats: "// Benchmark ... written by ABC on ..." 
    # and "// Benchmark ... written by ABC on ..." with different date formats
    sed '/written by ABC on/d' "$file1" > "$temp1"
    sed '/written by ABC on/d' "$file2" > "$temp2"
    
    # Also remove any other timestamp-like patterns that might vary
    # Remove lines that are just timestamps or dates
    sed -i '/^\/\/.*[0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\}/d' "$temp1" "$temp2" 2>/dev/null
    sed -i '/^\/\/.*[0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}/d' "$temp1" "$temp2" 2>/dev/null
    
    # Compare the cleaned files
    if cmp -s "$temp1" "$temp2"; then
        print_success "✓ $description are identical (ignoring timestamps)"
        local result=0
    else
        print_error "✗ $description differ beyond timestamps"
        echo "Differences found (timestamps ignored):"
        diff -u "$temp1" "$temp2" | head -100
        
        # Show only the real differences, not timestamp lines
        echo -e "\nReal differences (excluding timestamp lines):"
        diff -u "$file1" "$file2" | grep -v 'written by ABC on' | grep -v '^---' | grep -v '^+++' | head -50
        local result=1
    fi
    
    # Clean up temp files
    rm -f "$temp1" "$temp2"
    return $result
}

# Compare outputs while ignoring timestamps
compare_files_ignore_timestamp "$OLD_OUTPUT" "$NEW_OUTPUT" "Verilog outputs"
verilog_match=$?

# Function to compare console outputs
compare_console_outputs() {
    echo -e "\n=== Comparing Console Outputs ==="
    
    if [ ! -f "$OLD_LOG" ] || [ ! -f "$NEW_LOG" ]; then
        print_error "Missing one or both console output files"
        return 2
    fi
    
    # Remove timing information and other variable output
    local temp1=$(mktemp)
    local temp2=$(mktemp)
    
    # Clean up console output:
    # 1. Remove lines with "CPU time" or timing info
    # 2. Remove specific date/time patterns
    # 3. Remove memory usage stats (might vary slightly)
    sed -E '/CPU time|real time|user time|sys time|Elapsed time/d' "$OLD_LOG" | \
        sed -E '/[0-9]+\.[0-9]+[a-z]*/d' | \
        grep -v '^ABC' > "$temp1" 2>/dev/null || true
        
    sed -E '/CPU time|real time|user time|sys time|Elapsed time/d' "$NEW_LOG" | \
        sed -E '/[0-9]+\.[0-9]+[a-z]*/d' | \
        grep -v '^ABC' > "$temp2" 2>/dev/null || true
    
    if cmp -s "$temp1" "$temp2"; then
        print_success "✓ Console outputs are similar (timing differences ignored)"
        rm -f "$temp1" "$temp2"
        return 0
    else
        print_warning "Console outputs differ (may be timing-related)"
        echo "Differences in console output:"
        diff -u "$temp1" "$temp2" | head -30
        rm -f "$temp1" "$temp2"
        return 1
    fi
}

# Compare console outputs
compare_console_outputs
console_match=$?

# Summary
echo -e "\n${YELLOW}=== Test Summary ===${NC}"
echo "Command: $abc_command"
echo "Timestamp: $(date)"
echo -e "Exit codes: oldabc=$old_exit_code, new abc=$new_exit_code"
echo -e "Verilog match (timestamps ignored): $([ $verilog_match -eq 0 ] && print_success "YES" || print_error "NO")"
echo -e "Console output similarity: $([ $console_match -eq 0 ] && print_success "YES" || print_error "NO")"

if [ -f "$OLD_OUTPUT" ]; then
    echo -e "Old output: $OLD_OUTPUT ($(wc -l < "$OLD_OUTPUT") lines)"
fi
if [ -f "$NEW_OUTPUT" ]; then
    echo -e "New output: $NEW_OUTPUT ($(wc -l < "$NEW_OUTPUT") lines)"
fi

# Show the first few lines of each output for quick visual check
echo -e "\n${YELLOW}=== First few lines of outputs ===${NC}"
echo "Old output (first 5 lines):"
head -5 "$OLD_OUTPUT" 2>/dev/null || echo "  (file not found)"
echo ""
echo "New output (first 5 lines):"
head -5 "$NEW_OUTPUT" 2>/dev/null || echo "  (file not found)"

# Save test results
{
    echo "=== ABC Comparison Test Results ==="
    echo "Command: $abc_command"
    echo "Test date: $(date)"
    echo "Exit codes: old=$old_exit_code, new=$new_exit_code"
    echo "Verilog match (timestamps ignored): $([ $verilog_match -eq 0 ] && echo "PASS" || echo "FAIL")"
    echo "Console output similarity: $([ $console_match -eq 0 ] && echo "PASS" || echo "FAIL")"
    echo ""
    echo "Note: Timestamp differences in 'written by ABC on' lines are ignored."
} > test_results.txt

# Clean up if requested
if [ "${1:-}" = "--clean" ] || [ "${1:-}" = "-c" ]; then
    echo -e "\nCleaning up temporary files..."
    rm -f "$OLD_OUTPUT" "$NEW_OUTPUT" "$OLD_LOG" "$NEW_LOG"
fi

# Exit with appropriate code
# We consider it a success if Verilog outputs match (ignoring timestamps)
if [ $verilog_match -eq 0 ]; then
    print_success "\n✓ TEST PASSED: Verilog outputs match (timestamps ignored)"
    echo "  Note: Timestamp differences in '// Benchmark ... written by ABC on ...' are acceptable"
    exit 0
else
    print_error "\n✗ TEST FAILED: Verilog outputs differ beyond timestamps"
    exit 1
fi