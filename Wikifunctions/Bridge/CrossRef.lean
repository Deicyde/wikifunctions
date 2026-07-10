import Mathlib.Tactic.CrossRefAttribute
import Wikifunctions.Bridge.Z12427

/-!
# Queries for Mathlib cross-reference metadata

These meta definitions read Mathlib's public `Mathlib.CrossRef.tagExt` environment extension.
They are discovery and export tools only: finding a tag does not establish correctness of a
Wikifunctions implementation.
-/

namespace Wikifunctions.Bridge.CrossRef

open Lean Mathlib.CrossRef

/-- All cross-reference tags visible in an environment, sorted by external identifier. -/
meta def allTags (env : Environment) : Array Tag :=
  let state := PersistentEnvExtension.getState tagExt env
  state.2.flatten.appendList state.1 |>.qsort (·.tag < ·.tag)

/-- All Mathlib Wikidata tags visible in an environment. -/
meta def wikidataTags (env : Environment) : Array Tag :=
  (allTags env).filter (·.database == .wikidata)

/-- Mathlib declarations carrying a particular Wikidata identifier. -/
meta def declarationsForWikidata (env : Environment) (item : String) : Array Name :=
  (wikidataTags env).filterMap fun tag =>
    if tag.tag == item then some tag.declName else none

/-- Whether the Mathlib side of a metadata join is present in the current environment. -/
meta def hasMathlibTag (env : Environment) (metadata : ConceptMetadata) : Bool :=
  (declarationsForWikidata env metadata.wikidataItem).contains metadata.leanDeclaration

/-- Fail the current command elaboration unless a metadata join is present in the imported
Mathlib environment.  This checks discovery metadata at build time; it does not turn the tag
into evidence that a Wikifunction implementation satisfies its mathematical contract. -/
meta def assertMathlibTag (metadata : ConceptMetadata) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless hasMathlibTag env metadata do
    throwError "missing Mathlib Wikidata tag {metadata.wikidataItem} on \
      {metadata.leanDeclaration}"

/- Keep the pinned Q49008-to-`Nat.Prime` side of the Z12427 join live in CI. -/
run_cmd assertMathlibTag primeConceptMetadata

/-- Export-oriented records omit Mathlib's database discriminator, which is always Wikidata. -/
structure WikidataRecord where
  declaration : Name
  item : String
  comment : String
deriving Repr, DecidableEq

/-- Convert all Mathlib Wikidata tags to plain export-oriented records. -/
meta def exportWikidata (env : Environment) : Array WikidataRecord :=
  (wikidataTags env).map fun tag =>
    { declaration := tag.declName, item := tag.tag, comment := tag.comment }

end Wikifunctions.Bridge.CrossRef
