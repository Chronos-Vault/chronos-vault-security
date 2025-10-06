import { formalVerificationService } from '../server/security/formal-verification';

async function testFormalVerification() {
  try {
    console.log('🧪 Testing Formal Verification System\n');
    
    await formalVerificationService.initialize();
    
    const results = await formalVerificationService.verifyAllContracts();
    
    console.log('\n📈 Exporting Reports...\n');
    const jsonReports = await formalVerificationService.exportReports('json');
    
    jsonReports.forEach((report, contractName) => {
      console.log(`📄 ${contractName} Report Generated`);
    });
    
    console.log('\n✅ Formal Verification Test Complete!');
    
  } catch (error) {
    console.error('❌ Formal Verification Test Failed:', error);
    process.exit(1);
  }
}

testFormalVerification();
