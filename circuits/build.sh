#!/bin/bash
# Trinity Protocol - ZK Circuit Build Script
# Compiles Circom circuits and generates Solidity verifiers
#
# Usage: ./build.sh [circuit_name]
# Example: ./build.sh multisig_verification
#
# Requirements:
#   - circom >= 2.1.0
#   - snarkjs
#   - Node.js >= 18
#
# Trust Math, Not Humans

set -e

# Configuration
CIRCUIT_DIR="$(dirname "$0")"
BUILD_DIR="${CIRCUIT_DIR}/build"
PTAU_FILE="${CIRCUIT_DIR}/powersOfTau28_hez_final_14.ptau"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}=== Trinity Protocol ZK Circuit Builder ===${NC}"
echo ""

# Check dependencies
check_dependency() {
    if ! command -v $1 &> /dev/null; then
        echo -e "${RED}Error: $1 is not installed${NC}"
        echo "Install with: npm install -g $1"
        exit 1
    fi
}

check_dependency circom
check_dependency snarkjs

# Create build directory
mkdir -p "${BUILD_DIR}"

# Download Powers of Tau if not exists
if [ ! -f "$PTAU_FILE" ]; then
    echo -e "${YELLOW}Downloading Powers of Tau (one-time)...${NC}"
    curl -L https://hermez.s3-eu-west-1.amazonaws.com/powersOfTau28_hez_final_14.ptau -o "$PTAU_FILE"
fi

# Build a single circuit
build_circuit() {
    local CIRCUIT_NAME=$1
    local CIRCUIT_FILE="${CIRCUIT_DIR}/${CIRCUIT_NAME}.circom"
    
    if [ ! -f "$CIRCUIT_FILE" ]; then
        echo -e "${RED}Error: Circuit file not found: ${CIRCUIT_FILE}${NC}"
        return 1
    fi
    
    echo -e "${GREEN}Building ${CIRCUIT_NAME}...${NC}"
    
    # Step 1: Compile circuit
    echo "  [1/5] Compiling circuit..."
    circom "$CIRCUIT_FILE" \
        --r1cs \
        --wasm \
        --sym \
        --c \
        -o "${BUILD_DIR}" \
        -l "${CIRCUIT_DIR}/../node_modules"
    
    # Step 2: Generate proving key (Phase 2 trusted setup)
    echo "  [2/5] Generating proving key..."
    snarkjs groth16 setup \
        "${BUILD_DIR}/${CIRCUIT_NAME}.r1cs" \
        "$PTAU_FILE" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_0000.zkey"
    
    # Step 3: Contribute to ceremony (adds randomness)
    echo "  [3/5] Contributing to ceremony..."
    echo "trinity-protocol-$(date +%s)" | snarkjs zkey contribute \
        "${BUILD_DIR}/${CIRCUIT_NAME}_0000.zkey" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_final.zkey" \
        --name="Trinity Protocol Contribution" \
        -v
    
    # Step 4: Export verification key
    echo "  [4/5] Exporting verification key..."
    snarkjs zkey export verificationkey \
        "${BUILD_DIR}/${CIRCUIT_NAME}_final.zkey" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_vkey.json"
    
    # Step 5: Generate Solidity verifier
    echo "  [5/5] Generating Solidity verifier..."
    snarkjs zkey export solidityverifier \
        "${BUILD_DIR}/${CIRCUIT_NAME}_final.zkey" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_Verifier.sol"
    
    echo -e "${GREEN}✓ ${CIRCUIT_NAME} built successfully!${NC}"
    echo ""
    
    # Print circuit stats
    echo "Circuit Statistics:"
    snarkjs r1cs info "${BUILD_DIR}/${CIRCUIT_NAME}.r1cs"
    echo ""
}

# Generate witness for testing
generate_witness() {
    local CIRCUIT_NAME=$1
    local INPUT_FILE=$2
    
    if [ ! -f "$INPUT_FILE" ]; then
        echo -e "${RED}Error: Input file not found: ${INPUT_FILE}${NC}"
        return 1
    fi
    
    echo "Generating witness for ${CIRCUIT_NAME}..."
    
    node "${BUILD_DIR}/${CIRCUIT_NAME}_js/generate_witness.js" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_js/${CIRCUIT_NAME}.wasm" \
        "$INPUT_FILE" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_witness.wtns"
    
    echo -e "${GREEN}✓ Witness generated${NC}"
}

# Generate proof
generate_proof() {
    local CIRCUIT_NAME=$1
    
    echo "Generating proof for ${CIRCUIT_NAME}..."
    
    snarkjs groth16 prove \
        "${BUILD_DIR}/${CIRCUIT_NAME}_final.zkey" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_witness.wtns" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_proof.json" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_public.json"
    
    echo -e "${GREEN}✓ Proof generated${NC}"
}

# Verify proof
verify_proof() {
    local CIRCUIT_NAME=$1
    
    echo "Verifying proof for ${CIRCUIT_NAME}..."
    
    snarkjs groth16 verify \
        "${BUILD_DIR}/${CIRCUIT_NAME}_vkey.json" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_public.json" \
        "${BUILD_DIR}/${CIRCUIT_NAME}_proof.json"
}

# Main logic
if [ $# -eq 0 ]; then
    # Build all circuits
    echo "Building all circuits..."
    echo ""
    
    build_circuit "multisig_verification"
    build_circuit "vault_ownership"
    
    echo -e "${GREEN}=== All circuits built successfully! ===${NC}"
    echo ""
    echo "Output files in: ${BUILD_DIR}/"
    echo "  - *_Verifier.sol  : Solidity verifier contracts"
    echo "  - *_final.zkey    : Proving keys"
    echo "  - *_vkey.json     : Verification keys"
    echo "  - *.wasm          : WASM for proof generation"
else
    case $1 in
        "witness")
            generate_witness "$2" "$3"
            ;;
        "prove")
            generate_proof "$2"
            ;;
        "verify")
            verify_proof "$2"
            ;;
        *)
            build_circuit "$1"
            ;;
    esac
fi

echo ""
echo -e "${GREEN}Trust Math, Not Humans${NC}"
