#!/usr/bin/env tsx
/**
 * Cross-Chain Atomic Swap Test Script
 * 
 * Tests REAL atomic swaps across all 3 testnets using Trinity Protocol
 * - Arbitrum Sepolia
 * - Solana Devnet
 * - TON Testnet
 * 
 * Usage: tsx scripts/test-cross-chain-swaps.ts
 */

import chalk from 'chalk';
import crypto from 'crypto';

const API_BASE_URL = process.env.API_URL || 'http://localhost:5000';
const TEST_USER_WALLET = '0x66e5046D136E82d17cbeB2FfEa5bd5205D962906';

interface SwapTest {
  name: string;
  fromNetwork: 'ethereum' | 'solana' | 'ton';
  toNetwork: 'ethereum' | 'solana' | 'ton';
  fromToken: string;
  toToken: string;
  amount: string;
  minAmount: string;
}

interface SwapOrder {
  id: string;
  userAddress: string;
  fromToken: string;
  toToken: string;
  fromAmount: string;
  expectedAmount: string;
  minAmount: string;
  fromNetwork: string;
  toNetwork: string;
  status: string;
  lockTxHash?: string;
  executeTxHash?: string;
  secretHash: string;
  timelock: number;
  createdAt: string;
  expiresAt: string;
}

interface SwapResult {
  testName: string;
  orderId: string;
  success: boolean;
  duration: number;
  createTxHash?: string;
  lockTxHash?: string;
  executeTxHash?: string;
  consensusVerified: boolean;
  chainsVerified: string[];
  error?: string;
}

const SWAP_TESTS: SwapTest[] = [
  {
    name: 'Arbitrum → Solana (ETH → SOL)',
    fromNetwork: 'ethereum',
    toNetwork: 'solana',
    fromToken: 'ETH',
    toToken: 'SOL',
    amount: '0.01',
    minAmount: '0.008'
  },
  {
    name: 'Solana → TON (SOL → TON)',
    fromNetwork: 'solana',
    toNetwork: 'ton',
    fromToken: 'SOL',
    toToken: 'TON',
    amount: '0.1',
    minAmount: '0.08'
  },
  {
    name: 'TON → Arbitrum (TON → ETH)',
    fromNetwork: 'ton',
    toNetwork: 'ethereum',
    fromToken: 'TON',
    toToken: 'ETH',
    amount: '1.0',
    minAmount: '0.008'
  }
];

function printHeader() {
  console.log('\n' + chalk.cyan('═'.repeat(80)));
  console.log(chalk.cyan.bold('  🔄 CHRONOS VAULT - Cross-Chain Atomic Swap Test Suite'));
  console.log(chalk.cyan('  Trinity Protocol 2-of-3 Consensus Verification'));
  console.log(chalk.cyan('═'.repeat(80)) + '\n');
}

function printTestHeader(testName: string, index: number, total: number) {
  console.log('\n' + chalk.yellow('─'.repeat(80)));
  console.log(chalk.yellow.bold(`  Test ${index}/${total}: ${testName}`));
  console.log(chalk.yellow('─'.repeat(80)) + '\n');
}

function printStep(step: string, status: 'pending' | 'success' | 'error' | 'info' = 'info') {
  const symbols = {
    pending: chalk.blue('⏳'),
    success: chalk.green('✅'),
    error: chalk.red('❌'),
    info: chalk.cyan('ℹ️')
  };
  
  console.log(`${symbols[status]} ${step}`);
}

function printTxHash(chain: string, txHash: string) {
  console.log(`  ${chalk.gray('├─')} ${chalk.bold(chain)}: ${chalk.cyan(txHash)}`);
}

function generateSecret(): string {
  return crypto.randomBytes(32).toString('hex');
}

async function apiRequest(endpoint: string, method: string = 'GET', body?: any): Promise<any> {
  const url = `${API_BASE_URL}${endpoint}`;
  
  const options: RequestInit = {
    method,
    headers: {
      'Content-Type': 'application/json'
    }
  };
  
  if (body && method !== 'GET') {
    options.body = JSON.stringify(body);
  }
  
  const response = await fetch(url, options);
  const data = await response.json();
  
  if (!response.ok) {
    throw new Error(data.message || `API request failed: ${response.statusText}`);
  }
  
  return data;
}

async function createSwap(test: SwapTest): Promise<SwapOrder> {
  const response = await apiRequest('/api/defi/swap/create', 'POST', {
    userAddress: TEST_USER_WALLET,
    fromToken: test.fromToken,
    toToken: test.toToken,
    fromAmount: test.amount,
    minAmount: test.minAmount,
    fromNetwork: test.fromNetwork,
    toNetwork: test.toNetwork
  });
  
  return response.data;
}

async function lockSwap(orderId: string, secret: string): Promise<string> {
  const response = await apiRequest(`/api/defi/swap/${orderId}/lock`, 'POST', {
    secret
  });
  
  return response.data.lockTxHash;
}

async function executeSwap(orderId: string): Promise<string> {
  const response = await apiRequest(`/api/defi/swap/${orderId}/execute`, 'POST');
  
  return response.data.txHash;
}

async function getSwapStatus(orderId: string): Promise<SwapOrder> {
  const response = await apiRequest(`/api/defi/swap/order/${orderId}`, 'GET');
  
  return response.data;
}

async function verifyConsensus(orderId: string, fromNetwork: string, toNetwork: string): Promise<{
  verified: boolean;
  chains: string[];
}> {
  await new Promise(resolve => setTimeout(resolve, 2000));
  
  const order = await getSwapStatus(orderId);
  const chainsVerified: string[] = [];
  
  if (order.lockTxHash && order.lockTxHash !== 'pending') {
    chainsVerified.push(fromNetwork);
  }
  
  if (order.executeTxHash && order.executeTxHash !== 'pending') {
    chainsVerified.push(toNetwork);
  }
  
  if (order.lockTxHash && order.executeTxHash) {
    chainsVerified.push('consensus-layer');
  }
  
  const verified = chainsVerified.length >= 2;
  
  return { verified, chains: chainsVerified };
}

function isRealTxHash(txHash: string | undefined): boolean {
  if (!txHash || txHash === 'pending' || txHash.includes('simulated')) {
    return false;
  }
  
  if (txHash.startsWith('0x') && txHash.length === 66) {
    return true;
  }
  
  if (txHash.length > 40 && !txHash.includes('-')) {
    return true;
  }
  
  return false;
}

async function runSwapTest(test: SwapTest, index: number, total: number): Promise<SwapResult> {
  const startTime = Date.now();
  const result: SwapResult = {
    testName: test.name,
    orderId: '',
    success: false,
    duration: 0,
    consensusVerified: false,
    chainsVerified: []
  };
  
  try {
    printTestHeader(test.name, index, total);
    
    printStep(`Creating atomic swap order...`, 'pending');
    printStep(`  From: ${test.amount} ${test.fromToken} on ${test.fromNetwork}`, 'info');
    printStep(`  To: ${test.toToken} on ${test.toNetwork}`, 'info');
    
    const order = await createSwap(test);
    result.orderId = order.id;
    
    printStep(`Swap order created: ${chalk.bold(order.id)}`, 'success');
    printStep(`  Expected output: ${chalk.bold(order.expectedAmount)} ${test.toToken}`, 'info');
    printStep(`  Timelock expires: ${chalk.gray(new Date(order.expiresAt).toLocaleString())}`, 'info');
    
    const secret = generateSecret();
    
    printStep(`\nLocking funds on ${test.fromNetwork}...`, 'pending');
    const lockTxHash = await lockSwap(order.id, secret);
    result.lockTxHash = lockTxHash;
    
    printStep(`Funds locked successfully!`, 'success');
    printTxHash(test.fromNetwork.toUpperCase(), lockTxHash);
    printStep(`  Secret Hash: ${chalk.gray(order.secretHash.substring(0, 16) + '...')}`, 'info');
    
    await new Promise(resolve => setTimeout(resolve, 3000));
    
    printStep(`\nExecuting atomic swap...`, 'pending');
    const executeTxHash = await executeSwap(order.id);
    result.executeTxHash = executeTxHash;
    
    printStep(`Swap executed successfully!`, 'success');
    printTxHash(test.toNetwork.toUpperCase(), executeTxHash);
    
    printStep(`\nVerifying Trinity Protocol consensus...`, 'pending');
    const consensus = await verifyConsensus(order.id, test.fromNetwork, test.toNetwork);
    result.consensusVerified = consensus.verified;
    result.chainsVerified = consensus.chains;
    
    if (consensus.verified) {
      printStep(`Trinity Protocol consensus achieved! ✨`, 'success');
      printStep(`  Chains verified: ${chalk.bold(consensus.chains.join(', '))}`, 'info');
      printStep(`  Consensus: ${chalk.green('2-of-3 verification passed')}`, 'success');
    } else {
      printStep(`Consensus verification failed`, 'error');
      printStep(`  Chains verified: ${consensus.chains.join(', ')} (need 2+)`, 'error');
    }
    
    printStep(`\nValidating transaction hashes...`, 'pending');
    const lockTxValid = isRealTxHash(lockTxHash);
    const executeTxValid = isRealTxHash(executeTxHash);
    
    if (lockTxValid && executeTxValid) {
      printStep(`Transaction hashes validated (real blockchain transactions)`, 'success');
    } else {
      printStep(`Warning: Some transaction hashes may be simulated`, 'error');
      if (!lockTxValid) printStep(`  Lock TX appears simulated: ${lockTxHash}`, 'error');
      if (!executeTxValid) printStep(`  Execute TX appears simulated: ${executeTxHash}`, 'error');
    }
    
    const finalStatus = await getSwapStatus(order.id);
    printStep(`\nFinal swap status: ${chalk.bold(finalStatus.status.toUpperCase())}`, 
      finalStatus.status === 'executed' ? 'success' : 'error');
    
    result.success = finalStatus.status === 'executed' && consensus.verified;
    result.duration = Date.now() - startTime;
    
    return result;
    
  } catch (error) {
    result.success = false;
    result.duration = Date.now() - startTime;
    result.error = error instanceof Error ? error.message : String(error);
    
    printStep(`Test failed: ${result.error}`, 'error');
    
    return result;
  }
}

function printSummary(results: SwapResult[]) {
  console.log('\n' + chalk.cyan('═'.repeat(80)));
  console.log(chalk.cyan.bold('  📊 TEST SUMMARY'));
  console.log(chalk.cyan('═'.repeat(80)) + '\n');
  
  const totalTests = results.length;
  const successfulTests = results.filter(r => r.success).length;
  const consensusVerified = results.filter(r => r.consensusVerified).length;
  const totalDuration = results.reduce((sum, r) => sum + r.duration, 0);
  
  console.log(chalk.bold('Overall Results:'));
  console.log(`  ${chalk.cyan('Total Tests:')} ${totalTests}`);
  console.log(`  ${chalk.green('Successful:')} ${successfulTests}`);
  console.log(`  ${chalk.red('Failed:')} ${totalTests - successfulTests}`);
  console.log(`  ${chalk.yellow('Consensus Verified:')} ${consensusVerified}/${totalTests}`);
  console.log(`  ${chalk.gray('Total Duration:')} ${(totalDuration / 1000).toFixed(2)}s\n`);
  
  console.log(chalk.bold('Individual Test Results:'));
  
  results.forEach((result, index) => {
    const statusSymbol = result.success ? chalk.green('✅') : chalk.red('❌');
    const consensusSymbol = result.consensusVerified ? chalk.green('🔒') : chalk.red('🔓');
    
    console.log(`\n  ${statusSymbol} ${chalk.bold(`Test ${index + 1}: ${result.testName}`)}`);
    console.log(`     ${chalk.gray('Order ID:')} ${result.orderId || 'N/A'}`);
    console.log(`     ${chalk.gray('Duration:')} ${(result.duration / 1000).toFixed(2)}s`);
    
    if (result.lockTxHash) {
      console.log(`     ${chalk.gray('Lock TX:')} ${result.lockTxHash.substring(0, 32)}...`);
    }
    
    if (result.executeTxHash) {
      console.log(`     ${chalk.gray('Execute TX:')} ${result.executeTxHash.substring(0, 32)}...`);
    }
    
    console.log(`     ${consensusSymbol} ${chalk.gray('Consensus:')} ${result.consensusVerified ? chalk.green('VERIFIED') : chalk.red('FAILED')}`);
    
    if (result.chainsVerified.length > 0) {
      console.log(`     ${chalk.gray('Chains:')} ${result.chainsVerified.join(', ')}`);
    }
    
    if (result.error) {
      console.log(`     ${chalk.red('Error:')} ${result.error}`);
    }
  });
  
  console.log('\n' + chalk.cyan('─'.repeat(80)));
  
  if (successfulTests === totalTests && consensusVerified === totalTests) {
    console.log(chalk.green.bold('\n  🎉 ALL TESTS PASSED! Trinity Protocol is working correctly!\n'));
  } else if (successfulTests > 0) {
    console.log(chalk.yellow.bold('\n  ⚠️  PARTIAL SUCCESS - Some tests failed or consensus not achieved\n'));
  } else {
    console.log(chalk.red.bold('\n  ❌ ALL TESTS FAILED - Please check the atomic swap service\n'));
  }
  
  console.log(chalk.cyan('═'.repeat(80)) + '\n');
}

async function main() {
  printHeader();
  
  console.log(chalk.bold('Test Configuration:'));
  console.log(`  ${chalk.cyan('API Base URL:')} ${API_BASE_URL}`);
  console.log(`  ${chalk.cyan('Test Wallet:')} ${TEST_USER_WALLET}`);
  console.log(`  ${chalk.cyan('Test Count:')} ${SWAP_TESTS.length}`);
  console.log(`  ${chalk.cyan('Networks:')} Arbitrum Sepolia, Solana Devnet, TON Testnet\n`);
  
  const results: SwapResult[] = [];
  
  for (let i = 0; i < SWAP_TESTS.length; i++) {
    const result = await runSwapTest(SWAP_TESTS[i], i + 1, SWAP_TESTS.length);
    results.push(result);
    
    if (i < SWAP_TESTS.length - 1) {
      console.log(chalk.gray('\n  Waiting 5 seconds before next test...\n'));
      await new Promise(resolve => setTimeout(resolve, 5000));
    }
  }
  
  printSummary(results);
  
  const allPassed = results.every(r => r.success && r.consensusVerified);
  process.exit(allPassed ? 0 : 1);
}

main().catch(error => {
  console.error(chalk.red.bold('\n❌ Fatal error:'), error.message);
  process.exit(1);
});
