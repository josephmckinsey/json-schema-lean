import LeanUri

namespace JsonSchemaCodeGenTesting

-- Helper to create a simple URI for testing
def testURI (path : String) : LeanUri.URI :=
  LeanUri.URI.mk "http" (some "example.com") path none none

-- Helper to create a relative ref (for testing)
def mkRef (refStr : String) : LeanUri.URI ⊕ LeanUri.RelativeRef :=
  match LeanUri.RelativeRef.parse refStr with
  | .ok ref => .inr ref
  | .error _ =>
  let _ : Inhabited (LeanUri.URI ⊕ LeanUri.RelativeRef) := ⟨.inl (default)⟩
  panic! s!"Invalid ref: {refStr}"

end JsonSchemaCodeGenTesting
