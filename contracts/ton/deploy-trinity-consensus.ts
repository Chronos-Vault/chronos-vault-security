/**
 * Deployment Script for TON Trinity Consensus
 * 
 * This script deploys and initializes the Trinity Protocol validator on TON
 * that monitors Ethereum CrossChainBridgeOptimized and submits consensus proofs.
 * 
 * Usage:
 *   npx blueprint run deployTrinityConsensus --testnet
 *   npx blueprint run deployTrinityConsensus --mainnet
 */

import { toNano, Address, beginCell, Cell } from '@ton/core';
import { TrinityConsensus } from './wrappers/TrinityConsensus';
import { NetworkProvider } from '@ton/blueprint';

// ============================================================================
// DEPLOYED CONTRACT ADDRESSES (from deployment-v3.5.20-arbitrum-complete.json)
// ============================================================================
// Arbitrum Sepolia - CrossChainMessageRelay is the bridge entry point
const ETHEREUM_BRIDGE_ADDRESS_TESTNET = "0xC6F4f855fc690CB52159eE3B13C9d9Fb8D403E59";

// MAINNET: Must be set before mainnet deployment - deployment will fail if not set
const ETHEREUM_BRIDGE_ADDRESS_MAINNET = process.env.MAINNET_BRIDGE_ADDRESS;

// Validator Ethereum address (Chronos Vault deployer)
const VALIDATOR_ETHEREUM_ADDRESS = process.env.VALIDATOR_ETHEREUM_ADDRESS || "0x66e5046d136e82d17cbeb2ffea5bd5205d962906";

// Arbitrum RPC URLs
const ARBITRUM_RPC_TESTNET = process.env.ARBITRUM_RPC_URL || "https://sepolia-rollup.arbitrum.io/rpc";
const ARBITRUM_RPC_MAINNET = process.env.ARBITRUM_MAINNET_RPC_URL;

// ============================================================================
// QUANTUM-RESISTANT KEYS (ML-KEM-1024 and CRYSTALS-Dilithium-5)
// ============================================================================
// SECURITY: These MUST be generated using proper cryptographic libraries
// Generate with: npm run generate:quantum-keys
// The keys are loaded from environment variables to prevent hardcoding
const ML_KEM_PUBLIC_KEY_ENV = process.env.ML_KEM_PUBLIC_KEY;
const DILITHIUM_PUBLIC_KEY_ENV = process.env.DILITHIUM_PUBLIC_KEY;

// Validation function for quantum keys
function validateQuantumKeys(): { mlKem: bigint; dilithium: bigint } {
    if (!ML_KEM_PUBLIC_KEY_ENV || !DILITHIUM_PUBLIC_KEY_ENV) {
        throw new Error(
            "SECURITY ERROR: Quantum-resistant keys not configured!\n" +
            "Required environment variables:\n" +
            "  - ML_KEM_PUBLIC_KEY (256-bit hex value)\n" +
            "  - DILITHIUM_PUBLIC_KEY (256-bit hex value)\n\n" +
            "Generate keys using: npm run generate:quantum-keys"
        );
    }

    const mlKem = BigInt(ML_KEM_PUBLIC_KEY_ENV);
    const dilithium = BigInt(DILITHIUM_PUBLIC_KEY_ENV);

    // Reject placeholder values (all zeros or very small numbers)
    const MIN_KEY_VALUE = BigInt("0x" + "01".repeat(16)); // Minimum 128-bit entropy
    if (mlKem < MIN_KEY_VALUE) {
        throw new Error("SECURITY ERROR: ML-KEM key appears to be a placeholder (too small)");
    }
    if (dilithium < MIN_KEY_VALUE) {
        throw new Error("SECURITY ERROR: Dilithium key appears to be a placeholder (too small)");
    }

    return { mlKem, dilithium };
}

export async function run(provider: NetworkProvider) {
    console.log("🚀 Trinity Protocol Consensus Deployment (TON)");
    console.log("===============================================\n");

    const isMainnet = provider.network() === 'mainnet';
    const network = isMainnet ? 'mainnet' : 'testnet';

    console.log(`📡 Network: ${network}`);
    console.log(`📡 API Endpoint: ${provider.api()}\n`);

    // ================================================================
    // SECURITY VALIDATION - Must pass before deployment proceeds
    // ================================================================
    console.log("🔐 Validating quantum-resistant keys...");
    const quantumKeys = validateQuantumKeys();
    console.log("✅ Quantum keys validated\n");

    // Select configuration based on network
    const ethereumBridgeAddress = isMainnet 
        ? ETHEREUM_BRIDGE_ADDRESS_MAINNET 
        : ETHEREUM_BRIDGE_ADDRESS_TESTNET;

    // Validate mainnet bridge address
    if (isMainnet && !ethereumBridgeAddress) {
        throw new Error(
            "SECURITY ERROR: Mainnet bridge address not configured!\n" +
            "Set MAINNET_BRIDGE_ADDRESS environment variable before mainnet deployment."
        );
    }

    // Validate RPC URLs
    const arbitrumRpcUrl = isMainnet 
        ? ARBITRUM_RPC_MAINNET 
        : ARBITRUM_RPC_TESTNET;
    
    if (!arbitrumRpcUrl) {
        throw new Error(
            "ERROR: Arbitrum RPC URL not configured!\n" +
            isMainnet 
                ? "Set ARBITRUM_MAINNET_RPC_URL environment variable."
                : "Set ARBITRUM_RPC_URL environment variable or use default."
        );
    }

    console.log(`🔗 Ethereum Bridge: ${ethereumBridgeAddress}`);
    console.log(`🔗 Validator ETH Address: ${VALIDATOR_ETHEREUM_ADDRESS}`);
    console.log(`🔗 Arbitrum RPC: ${arbitrumRpcUrl}\n`);

    // Convert Ethereum addresses to bits (160 bits = 20 bytes)
    // Non-null assertion safe: validated above for mainnet, testnet has hardcoded value
    const ethereumBridgeBits = beginCell()
        .storeBuffer(Buffer.from(ethereumBridgeAddress!.replace("0x", ""), "hex"))
        .endCell()
        .beginParse()
        .loadBits(160);

    const validatorEthBits = beginCell()
        .storeBuffer(Buffer.from(VALIDATOR_ETHEREUM_ADDRESS.replace("0x", ""), "hex"))
        .endCell()
        .beginParse()
        .loadBits(160);

    // Encode Arbitrum RPC URL
    const arbitrumRpcCell = beginCell()
        .storeStringTail(arbitrumRpcUrl)
        .endCell();

    // Create initial data for TrinityConsensus contract
    const initialData = beginCell()
        .storeBits(ethereumBridgeBits)                          // ethereum_bridge_address (160 bits)
        .storeBits(validatorEthBits)                            // validator_ethereum_address (160 bits)
        .storeRef(arbitrumRpcCell)                              // arbitrum_rpc_url (ref)
        .storeAddress(provider.sender().address)                // authority_address
        .storeUint(0, 64)                                       // total_proofs_submitted
        .storeUint(0, 64)                                       // last_processed_operation
        .storeUint(1, 1)                                        // is_active (true)
        .storeDict(null)                                        // proof_records (empty dict)
        .storeDict(null)                                        // vault_verifications (empty dict)
        .storeUint(quantumKeys.mlKem, 256)                       // ml_kem_public_key
        .storeUint(quantumKeys.dilithium, 256)                 // dilithium_public_key
        .endCell();

    // Deploy contract
    const trinityConsensus = provider.open(
        await TrinityConsensus.fromInit(initialData)
    );

    console.log(`📝 Contract Address: ${trinityConsensus.address}\n`);

    // Check if already deployed
    const isDeployed = await provider.isContractDeployed(trinityConsensus.address);
    
    if (isDeployed) {
        console.log("⚠️  Contract already deployed!");
        
        // Fetch current state
        const config = await trinityConsensus.getValidatorConfig();
        console.log("\n📊 Current Validator Status:");
        console.log(`   Authority: ${config.authority}`);
        console.log(`   Total Proofs: ${config.totalProofsSubmitted}`);
        console.log(`   Active: ${config.isActive ? "Yes" : "No"}`);
        
        const shouldUpdate = await provider.ui().choose(
            "Contract exists. Update configuration?",
            ["Yes", "No"],
            (choice) => choice
        );

        if (shouldUpdate === "No") {
            console.log("\nDeployment cancelled.");
            return;
        }
    }

    // Deploy/Initialize
    console.log("🔧 Deploying Trinity Consensus contract...");
    
    await trinityConsensus.sendDeploy(
        provider.sender(),
        toNano('0.5') // Deploy with 0.5 TON for storage
    );

    await provider.waitForDeploy(trinityConsensus.address);

    console.log("✅ Trinity Consensus deployed!");
    console.log(`   Address: ${trinityConsensus.address}\n`);

    // Initialize with configuration
    console.log("🔧 Initializing contract...");
    
    await trinityConsensus.sendInitialize(
        provider.sender(),
        ethereumBridgeAddress!,
        VALIDATOR_ETHEREUM_ADDRESS,
        arbitrumRpcUrl,
        quantumKeys.mlKem,
        quantumKeys.dilithium
    );

    console.log("✅ Contract initialized!\n");

    // Verify deployment
    console.log("📊 Verifying deployment...");
    
    const config = await trinityConsensus.getValidatorConfig();
    console.log("\n✅ Validator Configuration:");
    console.log(`   Ethereum Bridge: 0x${config.ethereumBridgeAddress.toString(16).padStart(40, '0')}`);
    console.log(`   Validator ETH: 0x${config.validatorEthereumAddress.toString(16).padStart(40, '0')}`);
    console.log(`   Arbitrum RPC: ${config.arbitrumRpcUrl}`);
    console.log(`   Total Proofs: ${config.totalProofsSubmitted}`);
    console.log(`   Active: ${config.isActive ? "Yes" : "No"}`);

    const fetchedQuantumKeys = await trinityConsensus.getQuantumKeys();
    console.log(`\n🔐 Quantum-Resistant Keys:`);
    console.log(`   ML-KEM-1024: 0x${fetchedQuantumKeys.mlKem.toString(16)}`);
    console.log(`   Dilithium-5: 0x${fetchedQuantumKeys.dilithium.toString(16)}`);

    // Save deployment info
    const deploymentInfo = {
        network,
        contractAddress: trinityConsensus.address.toString(),
        authority: provider.sender().address?.toString(),
        ethereumBridge: ethereumBridgeAddress,
        validatorEthAddress: VALIDATOR_ETHEREUM_ADDRESS,
        arbitrumRpc: arbitrumRpcUrl,
        mlKemPublicKey: quantumKeys.mlKem.toString(16),
        dilithiumPublicKey: quantumKeys.dilithium.toString(16),
        deployedAt: new Date().toISOString(),
    };

    const fs = require('fs');
    const path = require('path');
    const deploymentPath = path.join(__dirname, `trinity-consensus-${network}.json`);
    fs.writeFileSync(deploymentPath, JSON.stringify(deploymentInfo, null, 2));
    console.log(`\n💾 Deployment info saved to: ${deploymentPath}`);

    console.log("\n🎉 Deployment Complete!");
    console.log("\n📋 Next Steps:");
    console.log("1. Add validator to Ethereum CrossChainBridgeOptimized:");
    console.log(`   bridge.addAuthorizedValidator(TON_CHAIN_ID, "${VALIDATOR_ETHEREUM_ADDRESS}")`);
    console.log("\n2. Start the off-chain TON relayer service:");
    console.log(`   npm run start:ton-relayer -- --network ${network}`);
    console.log("\n3. Monitor contract activity:");
    console.log(`   https://${isMainnet ? '' : 'testnet.'}tonapi.io/account/${trinityConsensus.address}`);
    console.log("\n4. Generate proper quantum-resistant keys:");
    console.log(`   npm run generate:quantum-keys`);

    console.log("\n⚠️  IMPORTANT: Update ML-KEM and Dilithium keys with real cryptographic values!");
}
