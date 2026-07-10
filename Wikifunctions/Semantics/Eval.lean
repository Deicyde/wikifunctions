import Wikifunctions.Model.Schema

/-!
# Wikifunctions evaluation semantics

This module gives the executable core of the Wikifunctions composition model.  It deliberately
depends only on semantic `ZObject`s: JSON decoding, schema validation, and WikiLean metadata are
separate layers.

The central design choices are:

* function and primitive identifiers are open `ZID` data, not a closed Lean enumeration;
* Z18-style argument references carry their key directly;
* Z7-style calls have an expression in callee position and keyed argument expressions;
* composition uses call-by-name substitution, so an unused argument is never evaluated;
* Z14 implementations are composition, primitive, or foreign code;
* implementation selection and all strict/foreign denotations are explicit runtime inputs;
* persistent-reference lookup is an explicit runtime input and is fuelled;
* fuel bounds evaluation depth, with exhaustion represented separately from semantic errors.

The evaluator treats quoted `ZObject`s as opaque data.  In particular, references below a quote
are not used as callees and argument-like objects below a quote are not substituted.
-/

namespace Wikifunctions.Semantics

open Wikifunctions.Model

/-! ## Composition syntax -/

/-- The evaluator-facing subset of Wikifunctions expressions.

`argument key` is the semantic content of a Z18 argument reference.  `call callee arguments` is
the semantic content of a Z7 call.  Quote payloads are already semantic ZObjects and are therefore
opaque to expression traversal. -/
inductive Expr where
  | literal : ZObject → Expr
  | argument : Key → Expr
  | quote : Raw → Expr
  | call : Expr → List (Key × Expr) → Expr
deriving Repr

/-- A keyed list of unevaluated call arguments. -/
abbrev Arguments := List (Key × Expr)

/-- Strictly evaluated keyed arguments supplied to a runtime or validation boundary. -/
abbrev EvaluatedArguments := List (Key × ZObject)

/-- Look up an unevaluated argument.  The first matching key wins.

Well-formed calls have unique keys; `validateArguments` checks this before dispatch. -/
def lookupArgument : Arguments → Key → Option Expr
  | [], _ => none
  | (candidate, value) :: arguments, key =>
      if candidate = key then some value else lookupArgument arguments key

@[simp]
theorem lookupArgument_nil (key : Key) : lookupArgument [] key = none := rfl

@[simp]
theorem lookupArgument_cons_same (key : Key) (value : Expr) (arguments : Arguments) :
    lookupArgument ((key, value) :: arguments) key = some value := by
  simp [lookupArgument]

@[simp]
theorem lookupArgument_cons_of_ne {candidate key : Key} (value : Expr)
    (arguments : Arguments) (h : candidate ≠ key) :
    lookupArgument ((candidate, value) :: arguments) key = lookupArgument arguments key := by
  simp [lookupArgument, h]

namespace Expr

/-- Substitute keyed call arguments into a composition body.

An inserted expression is returned unchanged rather than recursively substituted.  This is the
capture-free, call-by-name step: it keeps the inserted expression in the caller's context. -/
def instantiate (arguments : Arguments) (expression : Expr) : Expr :=
  match expression with
  | .literal value => .literal value
  | .argument key => (lookupArgument arguments key).getD (.argument key)
  | .quote payload => .quote payload
  | .call callee callArguments =>
      .call (instantiate arguments callee)
        (callArguments.map fun entry => (entry.1, instantiate arguments entry.2))
termination_by expression
decreasing_by
  · simp +arith
  · have hentry : sizeOf entry < sizeOf callArguments := by
      apply List.sizeOf_lt_of_mem
      assumption
    have hsnd : sizeOf entry.2 < sizeOf entry := by
      cases entry
      simp +arith
    have hlist : sizeOf callArguments < sizeOf (Expr.call callee callArguments) := by
      simp +arith
    exact Nat.lt_trans hsnd (Nat.lt_trans hentry hlist)

@[simp]
theorem instantiate_literal (arguments : Arguments) (value : ZObject) :
    instantiate arguments (.literal value) = .literal value := by
  simp [instantiate]

@[simp]
theorem instantiate_quote (arguments : Arguments) (payload : Raw) :
    instantiate arguments (.quote payload) = .quote payload := by
  simp [instantiate]

theorem instantiate_argument_of_lookup {arguments : Arguments} {key : Key} {value : Expr}
    (h : lookupArgument arguments key = some value) :
    instantiate arguments (.argument key) = value := by
  simp [instantiate, h]

theorem instantiate_argument_of_missing {arguments : Arguments} {key : Key}
    (h : lookupArgument arguments key = none) :
    instantiate arguments (.argument key) = .argument key := by
  simp [instantiate, h]

end Expr

/-! ## Implementations, registry, and selection -/

/-- A primitive implementation.

`lazyIf` is evaluator-aware because strict argument evaluation would destroy conditional
laziness.  Every other primitive is named by an open ZID and interpreted by `Runtime.strict`. -/
inductive Primitive where
  | lazyIf (conditionKey thenKey elseKey : Key)
  | strict (primitiveId : ZID)
deriving Repr

/-- Foreign source attached to a Z14 code implementation. -/
structure ForeignCode where
  language : ZID
  source : String
deriving Repr

/-- The three mutually exclusive Z14 implementation alternatives. -/
inductive Implementation where
  | composition (body : Expr)
  | primitive (value : Primitive)
  | foreign (code : ForeignCode)
deriving Repr

/-- Coarse implementation classes used by deterministic selection policies. -/
inductive ImplementationKind where
  | composition
  | primitive
  | foreign
deriving Repr, DecidableEq

namespace Implementation

/-- Classify an implementation without inspecting its payload. -/
def kind : Implementation → ImplementationKind
  | .composition _ => .composition
  | .primitive _ => .primitive
  | .foreign _ => .foreign

end Implementation

/-! ## Typed function signatures -/

/-- The evaluator-facing projection of one Z17 input declaration. -/
structure InputDeclaration where
  key : Key
  valueSchema : Schema.Checked
deriving Repr

/-- The typed projection of a Z8 signature used by evaluation contracts.

Validation fuel is explicit in each `Schema.Checked`; this keeps revision-sensitive validators
outside the evaluator kernel while making their exact use reproducible. -/
structure FunctionSignature where
  inputs : List InputDeclaration
  output : Schema.Checked
deriving Repr

namespace FunctionSignature

/-- Ordered input keys used by Z7 call validation and Z18 substitution. -/
def inputKeys (signature : FunctionSignature) : List Key :=
  signature.inputs.map (·.key)

/-- Check key uniqueness and require every declared validation bound to be positive. -/
def wellFormed (signature : FunctionSignature) : Bool :=
  ZObject.keysNoDup signature.inputKeys &&
    signature.inputs.all (fun input => input.valueSchema.fuel != 0) &&
    signature.output.fuel != 0

/-- Proposition-valued signature validity. -/
def WellFormed (signature : FunctionSignature) : Prop := signature.wellFormed = true

instance (signature : FunctionSignature) : Decidable signature.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Look up an already evaluated argument by its Z17 key. -/
def lookupEvaluatedArgument (arguments : EvaluatedArguments) (key : Key) : Option ZObject :=
  (arguments.find? fun entry => entry.1 == key).map (·.2)

/-- Validate already evaluated arguments against a Z17 projection by key, independently of JSON
object-member order.  Both sides must have unique keys and the same cardinality, so lookup cannot
silently accept a duplicate, missing, or unexpected argument. -/
def acceptsArguments (inputs : List InputDeclaration) (arguments : EvaluatedArguments) : Bool :=
  ZObject.keysNoDup (inputs.map (·.key)) &&
    ZObject.keysNoDup (arguments.map (·.1)) &&
    inputs.length == arguments.length &&
    inputs.all fun input =>
      match lookupEvaluatedArgument arguments input.key with
      | some value => input.valueSchema.accepts value
      | none => false

/-- Reordering two distinctly keyed values does not affect their schema validation. -/
theorem acceptsArguments_pair_swap (first second : InputDeclaration)
    (firstValue secondValue : ZObject) (hne : first.key ≠ second.key)
    (hfirst : first.valueSchema.accepts firstValue = true)
    (hsecond : second.valueSchema.accepts secondValue = true) :
    acceptsArguments [first, second]
      [(second.key, secondValue), (first.key, firstValue)] = true := by
  simp [acceptsArguments, lookupEvaluatedArgument, ZObject.keysNoDup,
    hne, Ne.symm hne, hfirst, hsecond]

/-- Validate already evaluated arguments against this signature. -/
def ArgumentsValid (signature : FunctionSignature) (arguments : EvaluatedArguments) : Prop :=
  acceptsArguments signature.inputs arguments = true

instance (signature : FunctionSignature) (arguments : EvaluatedArguments) :
    Decidable (signature.ArgumentsValid arguments) := by
  unfold ArgumentsValid
  infer_instance

end FunctionSignature

/-- A function's keyed input signature and its available implementations.

The signature is the typed projection of the function's Z8 definition. -/
structure FunctionDefinition where
  signature : FunctionSignature
  implementations : List Implementation
deriving Repr

namespace FunctionDefinition

/-- Check the local invariants needed for unambiguous function dispatch. -/
def wellFormed (definition : FunctionDefinition) : Bool :=
  definition.signature.wellFormed && !definition.implementations.isEmpty

/-- Proposition-valued local function-definition validity. -/
def WellFormed (definition : FunctionDefinition) : Prop := definition.wellFormed = true

instance (definition : FunctionDefinition) : Decidable definition.WellFormed := by
  unfold WellFormed
  infer_instance

end FunctionDefinition

/-- A finite, revision-pinned registry of function definitions. -/
abbrev Registry := List (ZID × FunctionDefinition)

namespace Registry

/-- Whether a registry contains a particular function identifier. -/
def containsFunctionId (registry : Registry) (functionId : ZID) : Bool :=
  registry.any fun entry => entry.1 == functionId

/-- Check registry uniqueness and every stored definition's local invariants. -/
def wellFormed : Registry → Bool
  | [] => true
  | (functionId, definition) :: registry =>
      definition.wellFormed &&
        (!containsFunctionId registry functionId && wellFormed registry)

/-- Proposition-valued registry validity. -/
def WellFormed (registry : Registry) : Prop := wellFormed registry = true

instance (registry : Registry) : Decidable registry.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Resolve a function identifier.  The first entry wins; registry construction should reject
duplicates before evaluation. -/
def lookup : Registry → ZID → Option FunctionDefinition
  | [], _ => none
  | (candidate, definition) :: registry, functionId =>
      if candidate = functionId then some definition else lookup registry functionId

@[simp]
theorem lookup_nil (functionId : ZID) : lookup [] functionId = none := rfl

@[simp]
theorem lookup_cons_same (functionId : ZID) (definition : FunctionDefinition)
    (registry : Registry) :
    lookup ((functionId, definition) :: registry) functionId = some definition := by
  simp [lookup]

@[simp]
theorem lookup_cons_of_ne {candidate functionId : ZID} (definition : FunctionDefinition)
    (registry : Registry) (h : candidate ≠ functionId) :
    lookup ((candidate, definition) :: registry) functionId = lookup registry functionId := by
  simp [lookup, h]

/-- Lookup from a well-formed registry preserves function-definition well-formedness. -/
theorem lookup_wellFormed {registry : Registry} {functionId : ZID}
    {definition : FunctionDefinition} (hregistry : Registry.WellFormed registry)
    (hlookup : lookup registry functionId = some definition) :
    FunctionDefinition.WellFormed definition := by
  induction registry with
  | nil => simp [lookup] at hlookup
  | cons entry registry ih =>
      rcases entry with ⟨candidate, current⟩
      simp only [Registry.WellFormed, Registry.wellFormed, Bool.and_eq_true] at hregistry
      have hcurrent : FunctionDefinition.WellFormed current := hregistry.1
      have hregistryTail : Registry.WellFormed registry := hregistry.2.2
      by_cases hcandidate : candidate = functionId
      · have hdefinition : current = definition := by
          simpa [lookup, hcandidate] using hlookup
        simpa [hdefinition] using hcurrent
      · apply ih hregistryTail
        simpa [lookup, hcandidate] using hlookup

end Registry

/-- An auditable deterministic implementation-selection policy.

Kinds are tried from left to right.  Within a kind, registry order is authoritative.  Omitting a
kind disables that implementation class. -/
structure SelectionPolicy where
  order : List ImplementationKind
deriving Repr

namespace SelectionPolicy

/-- The first implementation of a requested kind. -/
def firstOfKind (requested : ImplementationKind) : List Implementation → Option Implementation
  | [] => none
  | implementation :: implementations =>
      if implementation.kind = requested then some implementation
      else firstOfKind requested implementations

/-- Select an implementation according to an explicit kind priority. -/
def selectFromOrder (implementations : List Implementation) :
    List ImplementationKind → Option Implementation
  | [] => none
  | requested :: order =>
      match firstOfKind requested implementations with
      | some implementation => some implementation
      | none => selectFromOrder implementations order

/-- Select an implementation according to an explicit kind priority. -/
def select (policy : SelectionPolicy) (implementations : List Implementation) :
    Option Implementation :=
  selectFromOrder implementations policy.order

/-- Prefer auditable compositions, then strict/builtin primitives, then foreign code. -/
def compositionFirst : SelectionPolicy :=
  ⟨[.composition, .primitive, .foreign]⟩

/-- Permit only composition implementations. -/
def compositionOnly : SelectionPolicy := ⟨[.composition]⟩

end SelectionPolicy

/-! ## Outcomes and runtime boundaries -/

/-- Evaluation errors are semantic failures, distinct from insufficient fuel. -/
inductive EvalError where
  | unboundArgument (key : Key)
  | duplicateArgument (key : Key)
  | missingArgument (key : Key)
  | unexpectedArgument (key : Key)
  | calleeNotReference (value : ZObject)
  | unknownFunction (functionId : ZID)
  | noSelectedImplementation (functionId : ZID)
  | conditionNotBoolean (value : ZObject)
  | argumentSchemaMismatch (functionId : ZID)
  | outputSchemaMismatch (functionId : ZID) (value : ZObject)
  | referenceResolutionFailed (referenceId : ZID) (message : String)
  | strictPrimitiveFailed (primitiveId : ZID) (message : String)
  | foreignCodeFailed (language : ZID) (message : String)
deriving Repr

/-- A completed value, a semantic error, or exhaustion of the evaluator's depth budget. -/
inductive Outcome where
  | value (value : ZObject)
  | error (error : EvalError)
  | outOfFuel
deriving Repr

/-- An extensible denotation for strict/builtin primitives, indexed by an open ZID.

The result is an `Expr`, so the evaluator continues resolving it to a fixpoint instead of
mistaking an emitted Z9 or Z7 for a final value. -/
abbrev StrictDenotation := ZID → EvaluatedArguments → Except String Expr

/-- An explicit trust boundary for Python, JavaScript, or another foreign language.

The adapter must decode the foreign result into evaluator syntax; successful results re-enter
`eval` and therefore consume fuel until they reach an inner fixpoint. -/
abbrev ForeignDenotation := ForeignCode → EvaluatedArguments → Except String Expr

/-- Resolve a persistent Z9 identity to its evaluator-facing Z2K2 value.

`none` means that the reference is already an irreducible identity.  A successful target is an
`Expr`, rather than raw JSON, so persistent-object fetching and expression decoding remain an
explicit boundary outside the evaluator.  Repeated reference chains consume evaluation fuel. -/
abbrev ReferenceResolver := ZID → Except String (Option Expr)

/-- A finite, revision-pinned projection of persistent Z2K2 values after expression decoding. -/
abbrev PersistentStore := List (ZID × Expr)

namespace PersistentStore

/-- Look up a decoded Z2K2 value.  The first entry wins; audited stores should be unique. -/
def lookup : PersistentStore → ZID → Option Expr
  | [], _ => none
  | (candidate, value) :: store, referenceId =>
      if candidate = referenceId then some value else lookup store referenceId

/-- Turn a finite persistent-value snapshot into the open resolver interface. -/
def resolver (store : PersistentStore) : ReferenceResolver := fun referenceId =>
  .ok (store.lookup referenceId)

@[simp]
theorem lookup_cons_same (referenceId : ZID) (value : Expr) (store : PersistentStore) :
    lookup ((referenceId, value) :: store) referenceId = some value := by
  simp [lookup]

end PersistentStore

/-- All revision-sensitive or implementation-specific choices used during evaluation. -/
structure Runtime where
  registry : Registry
  policy : SelectionPolicy
  resolve : ReferenceResolver
  strict : StrictDenotation
  foreign : ForeignDenotation

/-! ## Call validation -/

/-- Whether an argument list contains a key. -/
def containsArgument (arguments : Arguments) (key : Key) : Bool :=
  arguments.any fun entry => entry.1 == key

/-- Find the first duplicate argument key, if any. -/
def firstDuplicateArgument? : Arguments → Option Key
  | [] => none
  | (key, _) :: arguments =>
      if containsArgument arguments key then some key else firstDuplicateArgument? arguments

/-- Find the first declared input missing from a call. -/
def firstMissingArgument? (arguments : Arguments) : List Key → Option Key
  | [] => none
  | key :: inputs =>
      if containsArgument arguments key then firstMissingArgument? arguments inputs else some key

/-- Find the first call argument not declared by the function. -/
def firstUnexpectedArgument? (inputs : List Key) : Arguments → Option Key
  | [] => none
  | (key, _) :: arguments =>
      if inputs.contains key then firstUnexpectedArgument? inputs arguments else some key

/-- Check that a Z7 call supplies each declared input exactly once and no other inputs. -/
def validateArguments (inputs : List Key) (arguments : Arguments) : Except EvalError Unit :=
  match firstDuplicateArgument? arguments with
  | some key => .error (.duplicateArgument key)
  | none =>
      match firstMissingArgument? arguments inputs with
      | some key => .error (.missingArgument key)
      | none =>
          match firstUnexpectedArgument? inputs arguments with
          | some key => .error (.unexpectedArgument key)
          | none => .ok ()

/-- Check a strict or foreign result against the declared Z8 output schema. -/
def validateOutput (functionId : ZID) (schema : Schema.Checked) : Outcome → Outcome
  | .value value =>
      if schema.accepts value then .value value
      else .error (.outputSchemaMismatch functionId value)
  | .error error => .error error
  | .outOfFuel => .outOfFuel

/-! ## Strict and lazy implementation dispatch -/

/-- Intermediate result of left-to-right strict argument evaluation. -/
inductive ArgumentsOutcome where
  | values (arguments : EvaluatedArguments)
  | error (error : EvalError)
  | outOfFuel
deriving Repr

/-- Evaluate every argument from left to right using `run`. -/
def evaluateArguments (run : Expr → Outcome) : Arguments → ArgumentsOutcome
  | [] => .values []
  | (key, expression) :: arguments =>
      match run expression with
      | .error error => .error error
      | .outOfFuel => .outOfFuel
      | .value value =>
          match evaluateArguments run arguments with
          | .values values => .values ((key, value) :: values)
          | .error error => .error error
          | .outOfFuel => .outOfFuel

/-- Construct a semantic Z40 Boolean value. -/
def booleanObject (value : Bool) : ZObject :=
  .object (.reference IDs.z40)
    [(Keys.z40k1, .reference (if value then IDs.z41 else IDs.z42))]

/-- Decode a Z40 Boolean value.  Bare Z41/Z42 references name identities and are not values. -/
def booleanValue? : ZObject → Option Bool
  | .object (.reference typeId) [(key, .reference valueId)] =>
      if typeId = IDs.z40 then
        if key = Keys.z40k1 then
          if valueId = IDs.z41 then some true
          else if valueId = IDs.z42 then some false
          else none
        else none
      else none
  | _ => none

/-- Evaluate one primitive.  Lazy conditionals receive the recursive evaluator itself and inspect
only the condition plus the selected branch. -/
def evalPrimitive (run : Expr → Outcome) (strict : StrictDenotation)
    (functionId : ZID) (signature : FunctionSignature)
    (primitive : Primitive) (arguments : Arguments) : Outcome :=
  match primitive with
  | .lazyIf conditionKey thenKey elseKey =>
      match lookupArgument arguments conditionKey with
      | none => .error (.missingArgument conditionKey)
      | some condition =>
          match run condition with
          | .error error => .error error
          | .outOfFuel => .outOfFuel
          | .value value =>
              match booleanValue? value with
              | none => .error (.conditionNotBoolean value)
              | some true =>
                  match lookupArgument arguments thenKey with
                  | none => .error (.missingArgument thenKey)
                  | some branch => run branch
              | some false =>
                  match lookupArgument arguments elseKey with
                  | none => .error (.missingArgument elseKey)
                  | some branch => run branch
  | .strict primitiveId =>
      match evaluateArguments run arguments with
      | .error error => .error error
      | .outOfFuel => .outOfFuel
      | .values values =>
          if FunctionSignature.acceptsArguments signature.inputs values then
            match strict primitiveId values with
            | .ok expression => validateOutput functionId signature.output (run expression)
            | .error message => .error (.strictPrimitiveFailed primitiveId message)
          else
            .error (.argumentSchemaMismatch functionId)

/-- Evaluate foreign code after strict left-to-right argument evaluation. -/
def evalForeign (run : Expr → Outcome) (foreign : ForeignDenotation) (functionId : ZID)
    (signature : FunctionSignature) (code : ForeignCode) (arguments : Arguments) : Outcome :=
  match evaluateArguments run arguments with
  | .error error => .error error
  | .outOfFuel => .outOfFuel
  | .values values =>
      if FunctionSignature.acceptsArguments signature.inputs values then
        match foreign code values with
        | .ok expression => validateOutput functionId signature.output (run expression)
        | .error message => .error (.foreignCodeFailed code.language message)
      else
        .error (.argumentSchemaMismatch functionId)

/-- Evaluate a callee while preserving a literal function identity for registry dispatch.

Ordinary literal references use `Runtime.resolve`.  A literal reference in Z7K1 is instead the
identity by which the function registry is indexed, so it must not be replaced by the function's
persistent Z2K2 object before dispatch.  Computed callees still use the recursive evaluator. -/
def evaluateCallee (run : Expr → Outcome) : Expr → Outcome
  | .literal (.reference functionId) => .value (.reference functionId)
  | callee => run callee

/-! ## Fuelled evaluator -/

/-- Evaluate an expression with a depth budget.

Every recursive evaluation receives the predecessor fuel.  For a composition, the body is
instantiated but its call arguments remain unevaluated until their argument references are used.
Thus the semantics is call-by-name, while strict and foreign boundaries explicitly force all
arguments. -/
def eval : Runtime → Nat → Expr → Outcome
  | _, 0, _ => .outOfFuel
  | runtime, fuel + 1, .literal (.reference referenceId) =>
      match runtime.resolve referenceId with
      | .error message => .error (.referenceResolutionFailed referenceId message)
      | .ok none => .value (.reference referenceId)
      | .ok (some target) => eval runtime fuel target
  | _, _ + 1, .literal value => .value value
  | _, _ + 1, .argument key => .error (.unboundArgument key)
  | _, _ + 1, .quote payload => .value (.quote payload)
  | runtime, fuel + 1, .call callee arguments =>
      match evaluateCallee (eval runtime fuel) callee with
      | .error error => .error error
      | .outOfFuel => .outOfFuel
      | .value (.reference functionId) =>
          match Registry.lookup runtime.registry functionId with
          | none => .error (.unknownFunction functionId)
          | some definition =>
              match validateArguments definition.signature.inputKeys arguments with
              | .error error => .error error
              | .ok () =>
                  match runtime.policy.select definition.implementations with
                  | none => .error (.noSelectedImplementation functionId)
                  | some (.composition body) => eval runtime fuel (body.instantiate arguments)
                  | some (.primitive primitive) =>
                      evalPrimitive (eval runtime fuel) runtime.strict functionId
                        definition.signature primitive arguments
                  | some (.foreign code) =>
                      evalForeign (eval runtime fuel) runtime.foreign functionId
                        definition.signature code arguments
      | .value value => .error (.calleeNotReference value)

/-! ## Kernel-checked evaluation laws -/

@[simp]
theorem eval_zero (runtime : Runtime) (expression : Expr) :
    eval runtime 0 expression = .outOfFuel := rfl

@[simp]
theorem eval_literal_string (runtime : Runtime) (fuel : Nat) (value : String) :
    eval runtime (fuel + 1) (.literal (.string value)) = .value (.string value) := rfl

@[simp]
theorem eval_literal_object (runtime : Runtime) (fuel : Nat) (type : ZObject)
    (fields : List (Key × ZObject)) :
    eval runtime (fuel + 1) (.literal (.object type fields)) =
      .value (.object type fields) := rfl

@[simp]
theorem eval_literal_list (runtime : Runtime) (fuel : Nat) (elementType : ZObject)
    (items : List ZObject) :
    eval runtime (fuel + 1) (.literal (.list elementType items)) =
      .value (.list elementType items) := rfl

@[simp]
theorem eval_literal_quote (runtime : Runtime) (fuel : Nat) (payload : Raw) :
    eval runtime (fuel + 1) (.literal (.quote payload)) = .value (.quote payload) := rfl

/-- An irreducible reference is a value/fixpoint. -/
theorem eval_reference_unresolved (runtime : Runtime) (fuel : Nat) (referenceId : ZID)
    (hresolve : runtime.resolve referenceId = .ok none) :
    eval runtime (fuel + 1) (.literal (.reference referenceId)) =
      .value (.reference referenceId) := by
  simp [eval, hresolve]

/-- A persistent reference is replaced by its evaluator-facing Z2K2 value and evaluation
continues with one less unit of fuel. -/
theorem eval_reference_resolved (runtime : Runtime) (fuel : Nat) (referenceId : ZID)
    (target : Expr) (hresolve : runtime.resolve referenceId = .ok (some target)) :
    eval runtime (fuel + 1) (.literal (.reference referenceId)) = eval runtime fuel target := by
  simp [eval, hresolve]

/-- Repeated persistent references resolve one step per unit of fuel until a value is reached. -/
theorem eval_reference_chain (runtime : Runtime) (fuel : Nat) (first second : ZID)
    (target : Expr)
    (hfirst : runtime.resolve first = .ok (some (.literal (.reference second))))
    (hsecond : runtime.resolve second = .ok (some target)) :
    eval runtime (fuel + 2) (.literal (.reference first)) = eval runtime fuel target := by
  rw [eval_reference_resolved runtime (fuel + 1) first
    (.literal (.reference second)) hfirst]
  exact eval_reference_resolved runtime fuel second target hsecond

/-- A bare Z41 identity becomes a complete Z40 value when the persistent resolver supplies its
Z2K2 representation. -/
theorem eval_true_identity (runtime : Runtime) (fuel : Nat)
    (hresolve : runtime.resolve IDs.z41 =
      .ok (some (.literal (booleanObject true)))) :
    eval runtime (fuel + 2) (.literal (.reference IDs.z41)) =
      .value (booleanObject true) := by
  rw [eval_reference_resolved runtime (fuel + 1) IDs.z41
    (.literal (booleanObject true)) hresolve]
  rfl

/-- Persistent-store failures are typed semantic errors, rather than silently becoming values. -/
theorem eval_reference_failed (runtime : Runtime) (fuel : Nat) (referenceId : ZID)
    (message : String) (hresolve : runtime.resolve referenceId = .error message) :
    eval runtime (fuel + 1) (.literal (.reference referenceId)) =
      .error (.referenceResolutionFailed referenceId message) := by
  simp [eval, hresolve]

/-- Literal function identities are stable in callee position, independently of data-reference
resolution. -/
@[simp]
theorem evaluateCallee_reference (run : Expr → Outcome) (functionId : ZID) :
    evaluateCallee run (.literal (.reference functionId)) = .value (.reference functionId) := rfl

@[simp]
theorem eval_unbound_argument (runtime : Runtime) (fuel : Nat) (key : Key) :
    eval runtime (fuel + 1) (.argument key) = .error (.unboundArgument key) := rfl

/-- Quote opacity: evaluation returns the quoted payload without traversing or resolving it. -/
@[simp]
theorem eval_quote (runtime : Runtime) (fuel : Nat) (payload : Raw) :
    eval runtime (fuel + 1) (.quote payload) = .value (.quote payload) := rfl

@[simp]
theorem booleanValue_booleanObject_true :
    booleanValue? (booleanObject true) = some true := by
  simp [booleanValue?, booleanObject]

@[simp]
theorem booleanValue_booleanObject_false :
    booleanValue? (booleanObject false) = some false := by
  have h : IDs.z42 ≠ IDs.z41 := by decide
  simp [booleanValue?, booleanObject, h]

@[simp]
theorem booleanValue_bare_reference (zid : ZID) :
    booleanValue? (.reference zid) = none := rfl

/-- A true lazy conditional evaluates exactly its selected branch.  No hypothesis mentions the
else expression or its evaluation, which is the formal laziness guarantee. -/
theorem evalPrimitive_lazyIf_true (run : Expr → Outcome) (strict : StrictDenotation)
    (functionId : ZID) (signature : FunctionSignature)
    (arguments : Arguments) (conditionKey thenKey elseKey : Key) (condition thenBranch : Expr)
    (hconditionLookup : lookupArgument arguments conditionKey = some condition)
    (hthenLookup : lookupArgument arguments thenKey = some thenBranch)
    (hcondition : run condition = .value (booleanObject true)) :
    evalPrimitive run strict functionId signature (.lazyIf conditionKey thenKey elseKey) arguments =
      run thenBranch := by
  simp [evalPrimitive, hconditionLookup, hcondition, hthenLookup]

/-- A false lazy conditional evaluates exactly its selected branch, independently of the then
expression. -/
theorem evalPrimitive_lazyIf_false (run : Expr → Outcome) (strict : StrictDenotation)
    (functionId : ZID) (signature : FunctionSignature)
    (arguments : Arguments) (conditionKey thenKey elseKey : Key) (condition elseBranch : Expr)
    (hconditionLookup : lookupArgument arguments conditionKey = some condition)
    (helseLookup : lookupArgument arguments elseKey = some elseBranch)
    (hcondition : run condition = .value (booleanObject false)) :
    evalPrimitive run strict functionId signature (.lazyIf conditionKey thenKey elseKey) arguments =
      run elseBranch := by
  simp [evalPrimitive, hconditionLookup, hcondition, helseLookup]

/-- A successful strict result re-enters the evaluator instead of being treated as a final raw
value. -/
theorem evalPrimitive_strict_success (run : Expr → Outcome) (strict : StrictDenotation)
    (functionId primitiveId : ZID) (signature : FunctionSignature)
    (arguments : Arguments) (values : EvaluatedArguments)
    (expression : Expr)
    (harguments : evaluateArguments run arguments = .values values)
    (hvalid : FunctionSignature.acceptsArguments signature.inputs values = true)
    (hstrict : strict primitiveId values = .ok expression) :
    evalPrimitive run strict functionId signature (.strict primitiveId) arguments =
      validateOutput functionId signature.output (run expression) := by
  simp [evalPrimitive, harguments, hvalid, hstrict]

/-- A successful foreign result also re-enters the evaluator. -/
theorem evalForeign_success (run : Expr → Outcome) (foreign : ForeignDenotation)
    (functionId : ZID) (signature : FunctionSignature) (code : ForeignCode)
    (arguments : Arguments) (values : EvaluatedArguments)
    (expression : Expr)
    (harguments : evaluateArguments run arguments = .values values)
    (hvalid : FunctionSignature.acceptsArguments signature.inputs values = true)
    (hforeign : foreign code values = .ok expression) :
    evalForeign run foreign functionId signature code arguments =
      validateOutput functionId signature.output (run expression) := by
  simp [evalForeign, harguments, hvalid, hforeign]

/-- Composition dispatch substitutes arguments without forcing them. -/
theorem eval_call_composition (runtime : Runtime) (fuel : Nat) (callee : Expr)
    (arguments : Arguments) (functionId : ZID) (definition : FunctionDefinition) (body : Expr)
    (hcallee : evaluateCallee (eval runtime fuel) callee = .value (.reference functionId))
    (hregistry : Registry.lookup runtime.registry functionId = some definition)
    (harguments : validateArguments definition.signature.inputKeys arguments = .ok ())
    (hselection : runtime.policy.select definition.implementations =
      some (.composition body)) :
    eval runtime (fuel + 1) (.call callee arguments) =
      eval runtime fuel (body.instantiate arguments) := by
  simp [eval, hcallee, hregistry, harguments, hselection]

/-- A constant composition does not evaluate any supplied argument.  In particular, this theorem
needs no premise asserting that an argument terminates or is even closed. -/
theorem eval_call_constant_composition (runtime : Runtime) (fuel : Nat) (callee : Expr)
    (arguments : Arguments) (functionId : ZID) (definition : FunctionDefinition)
    (value : ZObject)
    (hcallee : evaluateCallee (eval runtime (fuel + 1)) callee =
      .value (.reference functionId))
    (hregistry : Registry.lookup runtime.registry functionId = some definition)
    (harguments : validateArguments definition.signature.inputKeys arguments = .ok ())
    (hselection : runtime.policy.select definition.implementations =
      some (.composition (.literal value))) :
    eval runtime (fuel + 2) (.call callee arguments) =
      eval runtime (fuel + 1) (.literal value) := by
  rw [eval_call_composition runtime (fuel + 1) callee arguments functionId definition
    (.literal value) hcallee hregistry harguments hselection]
  simp

/-- End-to-end lazy-if dispatch through a ZID registry and an explicit selection policy. -/
theorem eval_call_lazyIf_true (runtime : Runtime) (fuel : Nat) (callee : Expr)
    (arguments : Arguments) (functionId : ZID) (definition : FunctionDefinition)
    (conditionKey thenKey elseKey : Key) (condition thenBranch : Expr)
    (hcallee : evaluateCallee (eval runtime fuel) callee = .value (.reference functionId))
    (hregistry : Registry.lookup runtime.registry functionId = some definition)
    (harguments : validateArguments definition.signature.inputKeys arguments = .ok ())
    (hselection : runtime.policy.select definition.implementations =
      some (.primitive (.lazyIf conditionKey thenKey elseKey)))
    (hconditionLookup : lookupArgument arguments conditionKey = some condition)
    (hthenLookup : lookupArgument arguments thenKey = some thenBranch)
    (hcondition : eval runtime fuel condition = .value (booleanObject true)) :
    eval runtime (fuel + 1) (.call callee arguments) = eval runtime fuel thenBranch := by
  simp [eval, hcallee, hregistry, harguments, hselection, evalPrimitive,
    hconditionLookup, hcondition, hthenLookup]

end Wikifunctions.Semantics
