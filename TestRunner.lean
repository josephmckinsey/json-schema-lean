import JsonSchema.Schema
import JsonSchema.Resolving
import JsonSchemaTesting.SchemaPointer
import JsonSchemaTesting.Resolving
import JsonSchemaTesting.Validation
import JsonSchemaCodeGenTesting.Tests
import JsonSchemaCodeGenTesting.ReferencesTests
import JsonSchemaCodeGenTesting.IntegrationTests
import UriTesting.Helpers

open Test Testing

def main : IO UInt32 := do
  TestM.run do
    allCodeGenTests
    allReferencesTests
    allIntegrationTests
    printSummary
  return 0
