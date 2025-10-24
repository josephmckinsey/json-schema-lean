#!/usr/bin/env bash
set -e

# Test code generation by converting JSON schemas to Lean and verifying they compile

echo "=== Testing JSON Schema to Lean Code Generation ==="
echo ""

# Create temporary directory for generated files
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Build the code generator
echo "Building schemaToJson..."
lake build schemaToJson
echo ""

# Track test results
TOTAL=0
PASSED=0
FAILED=0

# Process each JSON schema in test-schemas directory
for schema_file in test-schemas/*.json; do
    if [ ! -f "$schema_file" ]; then
        echo "No test schemas found in test-schemas/"
        exit 1
    fi

    TOTAL=$((TOTAL + 1))
    basename=$(basename "$schema_file" .json)
    lean_file="$TEMP_DIR/${basename}.lean"

    echo "Testing: $schema_file"

    # Generate Lean code
    if ! lake exe schemaToJson "$schema_file" "$lean_file" 2>&1; then
        echo "  ✗ FAILED: Code generation failed"
        FAILED=$((FAILED + 1))
        echo ""
        continue
    fi

    # Try to compile the generated code directly (just type-check, not run)
    echo "  Checking if generated code compiles..."
    if lake env lean "$lean_file" > /dev/null 2>&1; then
        echo "  ✓ PASSED: Generated code compiles"
        PASSED=$((PASSED + 1))
    else
        echo "  ✗ FAILED: Generated code does not compile"
        echo "  Generated file: $lean_file"
        FAILED=$((FAILED + 1))
        # Show compilation error for debugging
        echo "  Compilation error:"
        lake env lean "$lean_file" 2>&1 | head -n 20 | sed 's/^/    /'
    fi
    echo ""
done

# Print summary
echo "=== Summary ==="
echo "Total:  $TOTAL"
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo ""

if [ $FAILED -eq 0 ]; then
    echo "✓ All tests passed!"
    exit 0
else
    echo "✗ Some tests failed"
    exit 1
fi
