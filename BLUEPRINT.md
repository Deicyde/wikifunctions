# BLUEPRINT — how the Lean model matches deployed WikiLambda

1. This document pins every load-bearing declaration in this repo (`Wikifunctions/Core.lean`, `WikifunctionsEval.lean`, `Wikifunctions/Python/*`, `WikifunctionsSpecs.lean`) side by side against the exact WikiLambda artifact it models.
2. It cites a four-layer spec stack, from prose to production:
3. — Layer 1, prose spec: [Wikifunctions:Function_model](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model) — the canonical narrative definition of the function model.
4. — Layer 2, machine schemata: [function-schemata](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata) — `data/CANONICAL/*.yaml`, the JSON-Schema the platform enforces.
5. — Layer 3, community wiki content: the live API at https://www.wikifunctions.org/w/api.php — types, functions, and implementations that exist only as wiki ZObjects.
6. — Layer 4, deployed runtime: [function-orchestrator](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-orchestrator) / [function-evaluator](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator) plus [operations-deployment-charts](https://github.com/wikimedia/operations-deployment-charts) — what actually executes.
7. Every claim below ends in a `Check:` command or link. Run it (or open it) and compare the output against the quoted block beside it; nothing in this document asks to be believed without one.
8. `wikilambda_fetch` replies wrap each ZObject as a JSON-*encoded string*; parse with e.g. `python3 -c 'import json,sys; d=json.load(sys.stdin); [print(json.dumps(json.loads(v["wikilambda_fetch"]),indent=1)) for k,v in d.items() if k.startswith("Z")]'` or read it raw.
9. All live JSON, raw URLs, and Lean re-elaborations were verified 2026-07-02; repo state is branch `spec-audit`, commit `778a3e0`.
10. Where the model and the live system *disagree*, the row is flagged ⚠ with a D-number; the full divergence analysis (D1–D18, severities, recommended fixes) is `SPEC_AUDIT.md`.

---

## The object model and evaluator core — what `Core.lean` models and what it deliberately omits

`Wikifunctions/Core.lean` is 53 lines and declares exactly five concepts: ZIDs, a value universe, a composition AST, denotations, and a registry-parameterized evaluator. Each one is a deliberate image of a WikiLambda concept. This section pins every declaration twice — once to the prose spec ([Wikifunctions:Function_model](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model), the canonical home; anchors below are its live section headings) and once to the machine-enforced schema (`data/CANONICAL/*.yaml` in [function-schemata](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata); every raw URL below returned HTTP 200 on 2026-07-02) — and then pins the four load-bearing abstractions to deployed orchestrator source or a live API response.

### Concept inventory

| Lean (Core.lean) | WikiLambda concept | Function-model section | Schema pin (`data/CANONICAL/`) | Check |
|---|---|---|---|---|
| `abbrev ZID := String` — :16 | Z9/Reference: "a reference to the Z2K2/value of the ZObject with the given ID" | [#Z9/References](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z9/References) | `Z9.yaml:9` — `pattern: ^Z[1-9]\d*$` (a ZID *is* a string of this shape) | [raw Z9.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z9.yaml) |
| `inductive Val` (`nat`/`bool`/`rat`) — :20–24 | Literal instances of Z4/Types: Z13518, Z40, Z19677 | [#Z4/Types](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z4/Types) | `Z40.yaml:24–29` — `Z40K1` enum `[Z41, Z42]`. Z13518/Z19677 are community wiki types with **no** schema file; pinned live below | [raw Z40.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z40.yaml) |
| `Expr.arg : Nat → Expr` — :29 | Z18/Argument reference (the "argument reference" nodes of the composition example) | [#Composition](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Composition) | `Z18.yaml:11–12` — `Z18K1: $ref: Z6#/…/Z6_ZnKn` (a *key-id string*, see abstraction A) | [raw Z18.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z18.yaml) |
| `Expr.lit : Val → Expr` — :30 | Inline literal ZObject in argument position: "not a Z7/Function call, but a notation for the object of the given Z4/Type" | [#Z7/Function_calls](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z7/Function_calls) | `Z7.yaml:16–18` — `patternProperties: ^(Z[1-9]\d*)K[1-9]\d*?$ → Z1` (any ZObject may sit in an argument slot) | [raw Z7.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z7.yaml) |
| `Expr.call : ZID → List Expr → Expr` — :31 | Z7/Function call; `Z7K1` names the function | [#Z7/Function_calls](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z7/Function_calls) | `Z7.yaml:26–30` — `Z7K1: $ref: Z8`, listed under `required` | [raw Z7.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z7.yaml) |
| `abbrev Denotation := List Val → Option Val` — :34 | Z8/Function extensionally: `Z8K1` argument declarations → `Z8K2` return type, wrapped by the Z22 result (abstraction B) | [#Z8/Functions](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z8/Functions) | `Z8.yaml:19–21` — `Z8K1` (LIST_of_Z17), `Z8K2` (Z4); both `required` (:31–32) | [raw Z8.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z8.yaml) |
| `abbrev Registry := ZID → Option Denotation` — :38 | The wiki of Z2/Persistent objects; dereferencing "is to be replaced by the Z2K2/value from the Z2/Persistent object that has the Z2K1/id" | [#Persistent_and_transient](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Persistent_and_transient) | `Z2.yaml:19–23` — `Z2K1` (id, Z6) and `Z2K2` (value, Z1): the registry's key → value pair | [raw Z2.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z2.yaml) |
| `eval` / `evalArgs` — :43–51 | Evaluation of a `Z14K2` composition body: substitute and reduce to fixpoint; order "up to the evaluator" | [#Example_evaluation](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Example_evaluation), [#Evaluation_order](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Evaluation_order) | `Z14.yaml:12–14` (exactly-one-of `Z14K2`/K3/K4) and `:22–23` — `Z14K2: $ref: Z1` (the body is *any* ZObject; see abstraction/omission notes) | [raw Z14.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z14.yaml) |

The evaluator's `.call` clause (Core.lean:47) resolves the callee ZID through the registry exactly as a live `Z7K1` reference is resolved against the wiki, with a missing ZID collapsing to `none` (live: Z504/Z550).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=parse&format=json&page=Wikifunctions:Function_model&prop=sections" | jq -r '.parse.sections[].anchor'` — every anchor cited above appears in the output.

### The value-type pins

The three `Val` constructors (Core.lean:20–24) correspond to three deployed types. Z40 is spec-layer (schema above); **Z13518 and Z19677 are community wiki content — only a live fetch pins them.**

**`Val.nat : Nat` (Core.lean:21) ↔ Z13518 "Natural number".** Live `Z2K2`, trimmed to key structure:

```json
{ "Z1K1": "Z4", "Z4K1": "Z13518",
  "Z4K2": [ "Z3",
    { "Z1K1": "Z3", "Z3K1": "Z6", "Z3K2": "Z13518K1",
      "Z3K3": { …label: "value"… } } ],
  "Z4K3": "Z101" }
```

One key, `Z13518K1 : Z6` — an unbounded decimal string, so `Nat` is the exact carrier (no overflow gap). The declared validator `Z101` (`Z4K3`) is skipped in production (SPEC_AUDIT §1, layer 4), so well-formedness is a modelling precondition, not a live guarantee (cf. audit D12).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13518" | jq -r '.Z13518.wikilambda_fetch | fromjson | .Z2K2 | {zid: .Z4K1, key: .Z4K2[1].Z3K2, keytype: .Z4K2[1].Z3K1, validator: .Z4K3}'`

**`Val.bool : Bool` (Core.lean:22) ↔ Z40/Z41/Z42.** Live `Z2K2` of the two instances, verbatim and complete:

```json
Z41: { "Z1K1": "Z40", "Z40K1": "Z41" }     // true
Z42: { "Z1K1": "Z40", "Z40K1": "Z42" }     // false
```

`Z40.yaml:24–29` pins `Z40K1` to the enum `[Z41, Z42]` — exactly two inhabitants, so `Bool` is exact.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z41%7CZ42" | jq -r '.Z41.wikilambda_fetch, .Z42.wikilambda_fetch | fromjson | .Z2K2'`

**`Val.rat : ℚ` (Core.lean:23) ↔ Z19677 "Rational number".** Live key table (from `Z2K2.Z4K2`):

| key | type | label |
|---|---|---|
| `Z19677K1` | Z16659 (community sign enum) | sign |
| `Z19677K2` | Z13518 | numerator |
| `Z19677K3` | Z13518 | denominator |

`ℚ` models the sign/numerator/denominator triple up to fraction equality — unreduced representations quotient to the same `ℚ`, which is the correct notion of equality-of-meaning for the modelled theorems (SPEC_AUDIT §4, "Value universe"). Note Core.lean:19 correctly says just "rationals"; the *wrong* citation "Z70" lives in `WikifunctionsEval.lean:18` (audit D14 — Z70 fetches as Z550 Unknown reference).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z19677" | jq -r '.Z19677.wikilambda_fetch | fromjson | .Z2K2.Z4K2[1:] | map({key: .Z3K2, type: .Z3K1})'`

### The four load-bearing abstractions

Where Core.lean knowingly simplifies, each simplification is pinned to what the real system does, with the soundness argument for the modelled fragment.

**A. Positional `arg i` vs Z18 key-id reference.** Lean (Core.lean:29 and :45):

```lean
| arg  : Nat → Expr
-- …
| .arg i     => env[i]?
```

Live, a Z18 references by *key-id string* — from the actual composite body of coprime (`Z13702.Z2K2.Z14K2`, fetched):

```json
{ "Z1K1": "Z18", "Z18K1": "Z13701K1" }
```

(`Z18.yaml:11–12` types `Z18K1` as `Z6_ZnKn`, the `Z6.yaml:10–14` key pattern — never an index.) *Why sound:* in all six modelled composite bodies every Z18 references only the enclosing function's densely-numbered keys `ZxK1…ZxKn`, and every correctness theorem binds `env` in key order, so `arg i ↦ ZxK(i+1)` is an exact bijection — verified node-for-node (SPEC_AUDIT D16; documenting this at `Expr.arg` is audit recommendation 7).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13702" | jq -r '.Z13702.wikilambda_fetch | fromjson | .Z2K2.Z14K2.Z13522K1.Z13612K1'`

**B. `Option Val` vs the Z22/Z5 evaluation envelope.** Lean (Core.lean:34 and :40–42):

```lean
abbrev Denotation := List Val → Option Val
/- The registry-parameterized evaluator. Total: returns `none` on a missing
   ZID, a type error, or an out-of-range argument reference. -/
```

Live failure shape — divide 1 by 0 (`Z13546`), run through `wikifunctions_run` on 2026-07-02, trimmed to the comparable core:

```json
{ "Z1K1": "Z22",
  "Z22K1": "Z24",
  "Z22K2": { "Z1K1": { "Z7K1": "Z883", … }, "K1": [ …,
    { "K1": "errors",
      "K2": { "Z1K1": "Z5", "Z5K1": "Z28194",
              "Z5K2": { "Z28194K1": "1",
                        "Z28194K2": "Z13546K1",
                        "Z28194K3": "Z13546K2" } } }, … ] } }
```

`Z22.yaml:23–26` requires exactly `Z1K1`/`Z22K1`/`Z22K2`; on failure `Z22K1 = Z24` (void) and the Z5 error hangs under the `"errors"` key of the `Z22K2` metadata map — precisely the [#Z22/Evaluation_result](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z22/Evaluation_result) shape. *Why sound:* `none` collapses (Z24, errors→Z5) to a single failure point; every success-path theorem inspects only `some v`, and no provable statement in the repo depends on *which* error (SPEC_AUDIT §5 info list). The abstraction earns its keep by contrast: audit D3/D4 are exactly the two leaves in `WikifunctionsEval.lean` that totalize ÷0 instead of routing it into this `none` channel — the recommended fix (recommendation 3) is to use the channel this envelope justifies.

Check: `curl -s "https://www.wikifunctions.org/w/api.php" --data-urlencode "action=wikifunctions_run" --data-urlencode "format=json" --data-urlencode 'function_call={"Z1K1":"Z7","Z7K1":"Z13546","Z13546K1":{"Z1K1":"Z13518","Z13518K1":"1"},"Z13546K2":{"Z1K1":"Z13518","Z13518K1":"0"}}' | jq '.wikifunctions_run.data | fromjson | {Z22K1: .Z22K1, error: .Z22K2.K1[1]}'`

**C. Eager `evalArgs` vs the orchestrator's lazy table.** Lean (Core.lean:48–50) realizes every argument, left to right, before the call:

```lean
def evalArgs (R : Registry) (env : List Val) : List Expr → Option (List Val)
  | []      => some []
  | e :: es => (eval R env e).bind fun v =>
               (evalArgs R env es).bind fun vs => some (v :: vs)
```

The deployed orchestrator is eager too — except for a hardcoded table, `function-orchestrator/src/transpilation/utils.js:3–11` (the whole table, verbatim):

```js
const lazyFunctions = new Map();
// "if" lazily evaluates then and else clauses
lazyFunctions.set( 'Z802', new Set( [ 'K2', 'K3' ] ) );
// "try-catch" lazily evaluates inputs tryFunctionCall and errorHandler
// lazyFunctions.set( 'Z850', new Set( [ 'K1', 'K3' ] ) );
// "get error" lazily evaluates input functionCall
// lazyFunctions.set( 'Z853', new Set( [ 'K1' ] ) );
// "add debug log" lazily evaluates input functionCall
lazyFunctions.set( 'Z854', new Set( [ 'K1' ] ) );
```

consumed at `WFFunction.js:216–231` (`callWith` awaits `realize()` on every argument whose key is not in the set). The prose spec deliberately leaves this open — [#Evaluation_order](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Evaluation_order): "The evaluation order is up to the evaluator." *Why sound:* no ZID reachable from the six modelled composites is in the table; the modelled `if` is community `Z13846` (an ordinary Z8, eagerly realized live as well), and builtin `Z802` — the one lazy-load-bearing case, prerequisite for recursion — is declared out of scope (`WikifunctionsEval.lean:35–47`; SPEC_AUDIT §4 "Eager evaluation is faithful for everything modelled").

Check: `curl -s "https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-orchestrator/-/raw/main/src/transpilation/utils.js" | sed -n '1,11p'`

**D. One denotation per ZID vs `FirstImplementationSelector` over `Z8K4`.** Lean (Core.lean:38) resolves a ZID to at most one denotation:

```lean
abbrev Registry := ZID → Option Denotation
```

Live, a Z8 carries a *list* of implementations (`Z8.yaml:25–26`, `Z8K4: LIST_of_Z14`; [#Z8/Functions](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z8/Functions) shows add with three). Production picks one — `function-orchestrator/src/implementationSelector.js:44–56`, verbatim:

```js
class FirstImplementationSelector {
	* generate( implementations ) {
		for ( const implementation of implementations ) {
			yield implementation;
		}
	}
}
```

wired as the default at `src/OrchestratorConfig.js:49–50` (`implementationSelector = new FirstImplementationSelector()`) and driven over `Z8K4` at `src/transpilation/WFFunction.js:292`. *Why sound:* production runs the first implementation of the wiki-side (speed-re-ranked) `Z8K4` list, trying later ones only on error; a registry mapping each ZID to that first implementation's denotation is the deployed success-path behavior. SPEC_AUDIT §4 confirms the two Python programs proved in this repo (Z29182 for Z13701, Z13668 for Z13667) are the first-listed implementations — what the selector actually runs.

Check: `curl -s "https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-orchestrator/-/raw/main/src/implementationSelector.js" | sed -n '44,56p'`

### Deliberately omitted

`Z14.yaml:22–23` types a composite body as *any* ZObject; `Expr` (Core.lean:28–31) models the fragment the six proved composites use (audit D17 asks the docstring at :27 to say so). What is left out, and where the real system specifies it:

| Omitted from Core.lean | Real-system pin | Status in repo | Check |
|---|---|---|---|
| Recursion (builtin `Z802` with lazy K2/K3 + self-reference; no fixpoint/fuel in `eval`) | `utils.js:5` lazy entry; [#Evaluation_order](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Evaluation_order) fixpoint prose | Named out-of-scope frontier, `WikifunctionsEval.lean:37–47` (Z13612, Z13667, Z18194, …) | [raw utils.js](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-orchestrator/-/raw/main/src/transpilation/utils.js) |
| Computed callees and higher-order values (`Z7K1` itself a Z7/Z18; Z9 passed as argument) — `Expr.call` fixes the callee to a literal ZID | `RESOLVER.yaml:7–10` — any position accepts `anyOf [Z9, Z18, Z7]` | Acknowledged via audit D17; higher-order frontier (Z31679) listed at `WikifunctionsEval.lean:45–47` | [raw RESOLVER.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/RESOLVER.yaml) |
| The `Z22K2` metadata map (durations, hostnames, wasmtime fuel) — `Option` carries no metadata | The live envelope in abstraction B (every `K1`/`K2` pair beyond `errors`) | Unobservable in success-path theorems (SPEC_AUDIT §5) | [#Z22/Evaluation_result](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z22/Evaluation_result) |
| Generic/typed lists (Z881), Z99 quotes, and every value type beyond the three in `Val` | `Z1.yaml:15` admits Z99 at any tree level; [#Z881/Typed_lists](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z881/Typed_lists) | Explicit extension point: Core.lean:18–19 "Extend as new functions need new types" | [raw Z1.yaml](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/Z1.yaml) |

Check: `sed -n '16p;20,24p;28,31p;34p;38p;40,51p' Wikifunctions/Core.lean` — reproduces every Lean line cited in this section.

---

## The composite layer — six verified `Z14K2` bodies and eleven leaves (`WikifunctionsEval.lean`)

`WikifunctionsEval.lean` is a deep embedding of the Wikifunctions composition language: values `Val` (:58–62), a closed leaf library `Leaf` (:66–78) with Mathlib-backed denotations `Leaf.eval` (:89–101), the AST `Expr` (:82–85), and a total evaluator `eval`/`evalArgs` (:106–114). Six real composite implementations are transcribed as `Expr` terms and each is proved equal to a Mathlib oracle. This section puts every transcription next to the live `Z14K2` it claims to model.

**Reading conventions for the blocks below.**
- Live JSON was fetched via `wikilambda_fetch` (fetch date and parse recipe: orientation above).
- **Trimming:** each live body is the verbatim `Z14K2` with only the constant discriminator pairs `"Z1K1": "Z7"` (function call) and `"Z1K1": "Z18"` (argument reference) removed — every remaining `Z7K1`/`Z18K1` key implies them. Type-bearing `Z1K1`s on literals (`"Z13518"`) are kept. Nothing else is altered.
- **Argument encoding:** the Lean `.arg i` is positional; a live `Z18` references the enclosing function's key by name. The bijection `arg i ↦ Z<fn>K(i+1)` is exact for all six bodies (verified node-for-node; the abstraction itself is SPEC_AUDIT.md:79, D16).
- "Deployed" is witnessed by the function's live `Z8K4` implementation list containing the transcribed impl.

### 1. Are coprime — Z13701, impl [Z13702](https://www.wikifunctions.org/view/en/Z13702)

**Lean** (`WikifunctionsEval.lean:123-124`):
```lean
def coprimeComposite : Expr :=
  .call .natEq [.call .gcd [.arg 0, .arg 1], .lit (.nat 1)]
```

**Live `Z13702.Z14K2`** (label "coprime, composition of greatest common denominator ==1"; function Z13701 "are coprime (natural numbers)", `Z13518 × Z13518 → Z40`):
```json
{ "Z7K1": "Z13522",
  "Z13522K1": { "Z7K1": "Z13612",
                "Z13612K1": { "Z18K1": "Z13701K1" },
                "Z13612K2": { "Z18K1": "Z13701K2" } },
  "Z13522K2": { "Z1K1": "Z13518", "Z13518K1": "1" } }
```

Deployed: Z13701's `Z8K4 = [Z29182, Z13702]` — Z13702 attached (2 of 2). Theorems: `coprimeComposite_correct` (:127) — evaluates to `decide (Nat.Coprime a b)` — and `coprimeComposite_true_iff` (:131). The sanity example `coprime 64 99 = true` (:204) mirrors live tester Z13703 (first entry of Z13701's `Z8K3` above).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13701|Z13702"`

### 2. Least common multiple — Z13660, impl [Z13661](https://www.wikifunctions.org/view/en/Z13661)

**Lean** (`WikifunctionsEval.lean:136-137`):
```lean
def lcmComposite : Expr :=
  .call .div [.call .mul [.arg 0, .arg 1], .call .gcd [.arg 0, .arg 1]]
```

**Live `Z13661.Z14K2`** (label "lcm(m,n)=m*n/gcd(m,n)"; function Z13660 "least common multiple", `Z13518 × Z13518 → Z13518`):
```json
{ "Z7K1": "Z13546",
  "Z13546K1": { "Z7K1": "Z13539",
                "Z13539K1": { "Z18K1": "Z13660K1" },
                "Z13539K2": { "Z18K1": "Z13660K2" } },
  "Z13546K2": { "Z7K1": "Z13612",
                "Z13612K1": { "Z18K1": "Z13660K1" },
                "Z13612K2": { "Z18K1": "Z13660K2" } } }
```

Deployed: Z13660's `Z8K4 = [Z23481, Z14858, Z13661, Z34195]` — Z13661 attached (3 of 4). Theorem: `lcmComposite_correct` (:140), exploiting that `Nat.lcm` is definitionally `m * n / gcd m n`. Dividend/divisor roles match Z13548's `K1 // K2` (leaf table). ⚠ At `(0,0)` this theorem overstates live agreement — see the flagged D3 row below.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13660|Z13661"`

### 3. Kronecker delta — Z15849, impl [Z15852](https://www.wikifunctions.org/view/en/Z15852)

**Lean** (`WikifunctionsEval.lean:145-146`):
```lean
def kroneckerComposite : Expr :=
  .call .ite [.call .natEq [.arg 0, .arg 1], .lit (.nat 1), .lit (.nat 0)]
```

**Live `Z15852.Z14K2`** (label "Kronecker delta, composition"; function Z15849 "Kronecker delta", `Z13518 × Z13518 → Z13518`):
```json
{ "Z7K1": "Z13846",
  "Z13846K1": { "Z7K1": "Z13522",
                "Z13522K1": { "Z18K1": "Z15849K1" },
                "Z13522K2": { "Z18K1": "Z15849K2" } },
  "Z13846K2": { "Z1K1": "Z13518", "Z13518K1": "1" },
  "Z13846K3": { "Z1K1": "Z13518", "Z13518K1": "0" } }
```

Deployed: Z15849's `Z8K4 = [Z15854, Z15852, Z15853]` — Z15852 attached (2 of 3). Both literal branches (`"1"`, `"0"`) match. Theorem: `kroneckerComposite_correct` (:150) — evaluates to `if i = j then 1 else 0`.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z15849|Z15852"`

### 4. Nth r-simplex number — Z15483, impl [Z15487](https://www.wikifunctions.org/view/en/Z15487)

**Lean** (`WikifunctionsEval.lean:157-158`):
```lean
def simplexComposite : Expr :=
  .call .choose [.call .add [.arg 0, .call .dec [.arg 1]], .arg 1]
```

**Live `Z15487.Z14K2`** (label "nth r-simplex number, composition"; function Z15483 "nth r-simplex number", `Z13518 × Z13518 → Z13518`):
```json
{ "Z7K1": "Z13848",
  "Z13848K1": { "Z7K1": "Z13521",
                "Z13521K1": { "Z18K1": "Z15483K1" },
                "Z13521K2": { "Z7K1": "Z13582",
                              "Z13582K1": { "Z18K1": "Z15483K2" } } },
  "Z13848K2": { "Z18K1": "Z15483K2" } }
```

Deployed: Z15483's `Z8K4 = [Z15484, Z15487]` — Z15487 attached (2 of 2). Theorem: `simplexComposite_correct` (:162) — evaluates to `Nat.choose (n + (r - 1)) r` (`= Nat.multichoose n r`). Faithful even at `r = 0` because live `Z13582` truncates at zero exactly like Lean's `r - 1` (see the `dec` leaf row: Z13586's `if Z13582K1==0: return 0`).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z15483|Z15487"`

### 5. Bayes' theorem P(A|B) — Z20000, impl [Z20001](https://www.wikifunctions.org/view/en/Z20001)

**Lean** (`WikifunctionsEval.lean:167-168`):
```lean
def bayesComposite : Expr :=
  .call .ratDiv [.call .ratMul [.arg 0, .arg 1], .arg 2]
```

**Live `Z20001.Z14K2`** (label "Bayes', composition of multiply and divide"; function Z20000 "Bayes' theorem conditional probability P(A|B)", `Z19677 × Z19677 × Z19677 → Z19677`):
```json
{ "Z7K1": "Z19708",
  "Z19708K1": { "Z7K1": "Z19706",
                "Z19706K1": { "Z18K1": "Z20000K1" },
                "Z19706K2": { "Z18K1": "Z20000K2" } },
  "Z19708K2": { "Z18K1": "Z20000K3" } }
```

Deployed: Z20000's `Z8K4 = [Z20040, Z20002, Z20001]` — Z20001 attached (3 of 3). Theorem: `bayesComposite_correct` (:171) — evaluates to `pBA * pA / pB`. Structure and argument *order* are node-exact; note the live argument **labels** are `K1 = "P(A)"`, `K2 = "P(B|A)"`, so the Lean docstring/binder names are transposed (numerically harmless — multiplication commutes; SPEC_AUDIT.md:77, D15). ⚠ At `pB = 0` the theorem overstates live agreement — see the flagged D4 row below.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z20000|Z20001"`

### 6. Is perfect number — Z14933, impl [Z14934](https://www.wikifunctions.org/view/en/Z14934)

**Lean** (`WikifunctionsEval.lean:181-182`):
```lean
def perfectComposite : Expr :=
  .call .natEq [.call .sumProperDivisors [.arg 0], .arg 0]
```

**Live `Z14934.Z14K2`** (label "is perfect number, composition"; function Z14933 "is perfect number", `Z13518 → Z40`):
```json
{ "Z7K1": "Z13522",
  "Z13522K1": { "Z7K1": "Z13993",
                "Z13993K1": { "Z18K1": "Z14933K1" } },
  "Z13522K2": { "Z18K1": "Z14933K1" } }
```

Deployed: Z14933's `Z8K4 = [Z14934, Z14988, Z14945, Z15020, Z15017]` — Z14934 is **first-listed** of 5, i.e. what production's `FirstImplementationSelector` runs by default. Theorems: `perfectComposite_correct` (:185) — evaluates to `decide (∑ properDivisors = n)` — and `perfectComposite_perfect` (:193), which needs `0 < n` because the composite omits Mathlib `Nat.Perfect`'s positivity conjunct (documented at :190-192).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z14933|Z14934"`

### The eleven leaves

Constructors at `WikifunctionsEval.lean:66-78`; each denotation clause of `Leaf.eval` at :89-101 *is* the leaf's specification. Per row: constructor line / eval-clause line, the live function it stands for, and one deployed implementation whose decisive code line realizes the Lean denotation (all fetched 2026-07-02; each Check link fetches the function and that impl together).

| Leaf (ctor/eval) | Live ZID — label | Live signature | Lean denotation | Realizing impl — decisive line | Check |
|---|---|---|---|---|---|
| `natEq` (:68/:91) | Z13522 — "equality of natural numbers" | `Z13518² → Z40` | `decide (a = b)` | Z13533 (Python): `return Z13522K1 == Z13522K2` | [Z13522+Z13533](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13522%7CZ13533) |
| `gcd` (:67/:90) | Z13612 — "greatest common divisor" | `Z13518² → Z13518` | `Nat.gcd a b` | Z13642 (Python): `if (Z13612K1==0): return Z13612K2` (= `Nat.gcd`'s base clause; then Euclid `x, y = y, x % y`) | [Z13612+Z13642](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13612%7CZ13642) |
| `mul` (:69/:92) | Z13539 — "multiply two natural numbers" | `Z13518² → Z13518` | `a * b` | Z13540 (JS): `return Z13539K1 * Z13539K2;` | [Z13539+Z13540](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13539%7CZ13540) |
| `div` (:70/:93) | Z13546 — "divide natural numbers" | `Z13518² → Z13518` | `a / b` (floor; ⚠ total, see D3) | Z13548 (Python): `return Z13546K1 // Z13546K2` (floor division) | [Z13546+Z13548](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13546%7CZ13548) |
| `add` (:71/:94) | Z13521 — "add two Natural numbers" | `Z13518² → Z13518` | `a + b` | Z13573 (Python): `return Z13521K1+Z13521K2` | [Z13521+Z13573](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13521%7CZ13573) |
| `dec` (:72/:95) | Z13582 — "decrement natural number by one" | `Z13518 → Z13518` | `a - 1` (truncated at 0) | Z13586 (Python): `if Z13582K1==0: return 0` (zero-truncation, = Lean's `Nat` subtraction) | [Z13582+Z13586](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13582%7CZ13586) |
| `ite` (:73/:96) | Z13846 — "if (natural number output)" | `Z40 × Z13518² → Z13518` | `if c then t else e` | Z13847 (Python): `return Z13846K2 if Z13846K1 else Z13846K3` | [Z13846+Z13847](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13846%7CZ13847) |
| `choose` (:74/:97) | Z13848 — "binomial coefficient" | `Z13518² → Z13518` | `Nat.choose n k` | Z14852 (Python): `return math.comb(Z13848K1, Z13848K2)` (`math.comb(n,k)=0` for `k>n`, exactly `Nat.choose`) | [Z13848+Z14852](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13848%7CZ14852) |
| `sumProperDivisors` (:75/:98) | Z13993 — "sum of proper divisors" | `Z13518 → Z13518` | `∑ i ∈ Nat.properDivisors n, i` | Z13994 (Python): `return sdiv-Z13993K1` (σ(n) − n after a `i*i<=n` divisor sweep; returns 0 at n=0, matching `Nat.properDivisors 0 = ∅`) | [Z13993+Z13994](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13993%7CZ13994) |
| `ratMul` (:76/:99) | Z19706 — "multiply rational numbers" | `Z19677² → Z19677` | `a * b : ℚ` | Z20036 (JS): `let numerator = Z19706K1.K1*Z19706K2.K1;` (num×num over den×den) | [Z19706+Z20036](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z19706%7CZ20036) |
| `ratDiv` (:77/:100) | Z19708 — "divide rational numbers" | `Z19677² → Z19677` | `a / b : ℚ` (⚠ total, see D4) | Z20037 (JS): `let numerator = Z19708K1.K1*Z19708K2.K2;` (invert-and-multiply) | [Z19708+Z20037](https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z19708%7CZ20037) |

### ⚠ Flagged: the two known ÷0 divergences (SPEC_AUDIT D3/D4)

The two rows marked ⚠ above are the *only* semantic leaks in this file: Lean's total division returns junk `0` where every live implementation raises error **Z28194** (division by zero). Confirmed by fetch, not suspicion (SPEC_AUDIT.md:47, :49).

**D3 — `.div` at divisor 0.** Lean (`WikifunctionsEval.lean:93`) is total `Nat.div` (`a / 0 = 0`):
```lean
| .div,               [.nat a, .nat b] => some (.nat (a / b))
```
Live Z13548 guards (verbatim; Z14084 (JS) and composite Z34175 guard likewise, SPEC_AUDIT.md:47):
```python
if (Z13546K2==0):
	Wikifunctions.Error("Z28194",[str(Z13546K1),"Z13546K1","Z13546K2"])
```
Consequence: `lcmComposite_correct` (:140-142) quantifies over all `a b`, so at `(0,0)` it proves `some (.nat 0)` while live `lcm(0,0)` via Z13661 reaches `divide(0,0)` (gcd(0,0)=0) and returns a Z5 error envelope. `(0,0)` is the only diverging input.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13548"`

**D4 — `.ratDiv` at divisor 0.** Lean (`WikifunctionsEval.lean:100`) is total ℚ division (`x / 0 = 0`):
```lean
| .ratDiv,            [.rat a, .rat b] => some (.rat (a / b))
```
Live guards (verbatim), Z20037 (JS) and Z19710 (Python):
```javascript
if (Z19708K2.K1===0n){
	Wikifunctions.Error("Z28194",[Z19708K1.K1+"/"+Z19708K1.K2,"Z19708K1","Z19708K2"]);
```
```python
if Z19708K2==0:
	Wikifunctions.Error("Z28194",[str(Z19708K1),"Z19708K1","Z19708K2"])
```
Consequence: `bayesComposite_correct` (:171-173) carries no `pB ≠ 0` hypothesis, so it proves `some (.rat 0)` on the entire `pB = 0` hyperplane where live returns a Z5 error. Recommended fix (SPEC_AUDIT.md:140): make both leaves return `none` on zero divisor — `none` is already this model's error channel — and restate the two theorems.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z20037|Z19710"`

---

## The imperative-Python layer — two deployed programs, embedded and proved

**Files:** `Wikifunctions/Python/Imp.lean` (the deep embedding), `Z13701Prog.lean` / `Z13701.lean` (coprimality), `Z13667Prog.lean` / `Z13667.lean` (factorial), `DiffDriver.lean` (difftest binary), `native/` (empirical + cross-prover anchors).

The chain a reviewer should be able to walk by eye: **live wiki source** (the `Z14K3.Z16K2` string of an implementation ZObject, fetched below) → **AST-as-data transcription** (`*Prog.lean`) → **fuel-interpreter semantics** (`Imp.lean`) → **theorem against Mathlib's own spec** (`Z13701.lean` / `Z13667.lean`, axioms `[propext, Classical.choice, Quot.sound]`) → **empirical/deductive trust anchors** (`native/`) → **pins on the deployed runtime** (RustPython 0.5.0 on wasm32-wasip1 under wasmtime, 10¹⁰ fuel).

### Construct inventory — every `Imp` constructor ↔ its Python construct

The embedding is deliberately tiny: it contains exactly the constructs the two deployed programs use, nothing else.

| Lean constructor | Imp.lean | Python construct modelled | In Z13701 impl **Z29182** | In Z13667 impl **Z13668** |
|---|---|---|---|---|
| `State` (assoc list, `get`/`set`) | `Imp.lean:46`, `:50-52`, `:57-58` | the function-local variable frame (names → non-negative ints; unbound reads = `0` in the model) | locals `Z13701K1`, `Z13701K2` | locals `Z13667K1`, `k`, `i` |
| `Expr.var` | `Imp.lean:70` | local variable reference | `Z13701K2` in the guard; `Z13701K1 % Z13701K2` | `k`, `i`, `Z13667K1` |
| `Expr.lit` | `Imp.lean:71` | integer literal | *none in the AST* — the `0` of `!= 0` is absorbed into `Cond.ne0`, the `1` of `return … == 1` is meta-level in `runProgram` (`Z13701Prog.lean:46`) | `.lit 1` = the implicit `+1` step of `range` (`Z13667Prog.lean:34`); the `1`s of `k=1` / `range(1,…)` are meta-level in `facInit` (`Z13667Prog.lean:42`) |
| `Expr.add` | `Imp.lean:72` | `+` | unused | `i + 1` — `range`'s implicit increment; the source-level `Z13667K1+1` bound is absorbed into the `≤` guard (see desugaring below) |
| `Expr.mul` | `Imp.lean:73` | `*` (here via augmented `*=`) | unused | `k*=i` → `.mul (.var facK) (.var facI)` (`Z13667Prog.lean:34`) |
| `Expr.mod` | `Imp.lean:74`, eval `:99` | `%` on non-negative ints | line 3: `Z13701K1 % Z13701K2` → `Z13701Prog.lean:31` | unused |
| `Cond.ne0` | `Imp.lean:80` | `while e != 0` | line 2: `while Z13701K2 != 0:` → `Z13701Prog.lean:35` | unused |
| `Cond.le` | `Imp.lean:81` | `e₁ <= e₂` — exists **only** as the desugared `for`-range guard | unused | line 3: `for i in range(1,Z13667K1+1)` → `while i <= Z13667K1` (`Z13667Prog.lean:38`) |
| `Stmt.passign` | `Imp.lean:88`, semantics `doPassign` `:109-112` | simultaneous tuple assignment `x, y = e₁, e₂` (both RHS evaluated in the *old* state) | line 3: the tuple swap → `Z13701Prog.lean:30-31` | `k*=i` fused with the loop increment into one parallel assign (`Z13667Prog.lean:33-34`) |
| `Stmt.while_` | `Imp.lean:89`, fuel semantics `Stmt.run` `:116-131` | `while` loop | line 2 | the `for` loop, after desugaring |
| `Stmt.seq` | `Imp.lean:90` | statement sequencing `;` / newline | **unused by both embedded programs** — each is a single loop; initialization lives in the initial-state *data* (`initState` `Z13701Prog.lean:38-39`, `facInit` `Z13667Prog.lean:41-42`), not in seq'd assignments. Only `Stmt.run` (`Imp.lean:118-121`) mentions it. |

Two semantic caveats a reviewer should know (both from `SPEC_AUDIT.md` §3):

- **`%` by zero (D5):** `Imp.lean:99` uses Lean's total `Nat.mod` (`x % 0 = x`); real Python raises `ZeroDivisionError`. Structurally unreachable here — Z13701's `%` executes only under the `while Z13701K2 != 0` guard evaluated in the *same* state (`Imp.lean:122-131`), and Z13668 uses no `%` — so no current theorem is affected.
- **Twin definitions (D9):** `Z13701.lean` *restates* the program (`Z13701.lean:44-59,136-139`) instead of importing `Z13701Prog.lean`; `DiffDriver.lean:1` imports only the Prog twin. The two are token-identical today but formally unconnected. The Z13667 pair is wired correctly (`Z13667.lean:1` imports `Z13667Prog`).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z29182%7CZ13668" | python3 -c "import json,sys; d=json.load(sys.stdin); [print(json.loads(d[z]['wikilambda_fetch'])['Z2K2']['Z14K3']['Z16K2'], '\n---') for z in ('Z29182','Z13668')]"`

### Side-by-side: the live deployed Python vs the Lean transcription

#### Z13701 "are coprime (natural numbers)" — implementation Z29182

Z13701's live implementation list `Z8K4 = [Z29182, Z13702]`; `Z29182.Z2K2.Z14K1 = Z13701`, code language `Z16K1 = Z610` (Python). Fetched 2026-07-02; the live source is **TAB-indented** with no trailing newline (the docstring quote at `Z13701Prog.lean:14-19` renders it with 4 spaces — token-identical, whitespace differs):

```python
def Z13701(Z13701K1, Z13701K2):
	while Z13701K2 != 0:
		Z13701K1, Z13701K2 = Z13701K2, Z13701K1 % Z13701K2
	return Z13701K1 == 1
```

`Z13701Prog.lean:30-46` (the AST as data; variable names are the deployed key names, `Z13701Prog.lean:25,27`):

```lean
def loopBody : Stmt :=
  .passign varA varB (.var varB) (.mod (.var varA) (.var varB))

def loop : Stmt :=
  .while_ (.ne0 (.var varB)) loopBody

def initState (a b : Nat) : State :=
  (State.set ([] : State) varA a).set varB b

def runProgram (a b : Nat) : Option Bool :=
  match loop.run (b + 1) (initState a b) with
  | none => none
  | some t => some (State.get t varA == 1)
```

Node-by-node: `while Z13701K2 != 0` ↔ `.while_ (.ne0 (.var varB))`; the simultaneous tuple assignment ↔ `.passign` (both RHS read the old state — `doPassign`, `Imp.lean:106-112`); `return Z13701K1 == 1` ↔ the final `== 1` on `varA`. Fuel `b + 1` is *proved* sufficient (termination is part of the theorem, not an assumption).

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z29182" | python3 -c "import json,sys; print(repr(json.loads(json.load(sys.stdin)['Z29182']['wikilambda_fetch'])['Z2K2']['Z14K3']['Z16K2']))"`

#### Z13667 "factorial" — implementation Z13668

Z13667's live `Z8K4 = [Z14899, Z13668, Z14898, Z13863]`; `Z13668.Z2K2.Z14K1 = Z13667`, `Z16K1 = Z610`. Fetched 2026-07-02; live source is 4-space-indented with **no spaces** around `=`, `*=`, `,`, `+` (the docstring quote at `Z13667Prog.lean:8-14` adds spaces — token-identical modulo whitespace):

```python
def Z13667(Z13667K1):
    k=1
    for i in range(1,Z13667K1+1):
        k*=i
    return k
```

`Z13667Prog.lean:33-49`:

```lean
def facBody : Stmt :=
  .passign facK facI (.mul (.var facK) (.var facI)) (.add (.var facI) (.lit 1))

def facLoop : Stmt :=
  .while_ (.le (.var facI) (.var facN)) facBody

def facInit (n : Nat) : State :=
  ((State.set ([] : State) facN n).set facK 1).set facI 1

def runFac (n : Nat) : Option Nat :=
  match facLoop.run (n + 1) (facInit n) with
  | none => none
  | some t => some (State.get t facK)
```

**The `for` → `while` desugaring, made explicit** (stated at `Z13667Prog.lean:16-19`): `for i in range(1, Z13667K1+1): k *= i` becomes

- `i = 1` — `range`'s start, folded into the initial state (`facInit`, `Z13667Prog.lean:42`, alongside `k = 1`);
- guard `i <= Z13667K1` — `range`'s *exclusive* bound `Z13667K1+1` becomes the *inclusive* `≤ Z13667K1` (`Cond.le`, `Z13667Prog.lean:38`); this is where the source's `+1` goes;
- body `k, i = k*i, i+1` — the augmented assignment `k*=i` and `range`'s implicit increment, fused into one parallel assignment (`Z13667Prog.lean:34`); the `.lit 1` and `.add` in the AST come from this implicit increment, not from any literal token in the source.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13668" | python3 -c "import json,sys; print(repr(json.loads(json.load(sys.stdin)['Z13668']['wikilambda_fetch'])['Z2K2']['Z14K3']['Z16K2']))"`

### The two main theorems

Verbatim, with their in-file axiom checks. Both were re-elaborated 2026-07-02; both `#print axioms` report exactly `[propext, Classical.choice, Quot.sound]` (Lean's three standard axioms — no `sorry`, no extra axioms).

`Wikifunctions/Python/Z13701.lean:143-144` (axiom check at `:176`):

```lean
theorem runProgram_eq_coprime (a b : Nat) :
    runProgram a b = some (decide (Nat.Coprime a b)) := by
```
```lean
#print axioms Wikifunctions.Python.runProgram_eq_coprime
-- 'Wikifunctions.Python.runProgram_eq_coprime' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
```

`Wikifunctions/Python/Z13667.lean:144` (axiom check at `:168`):

```lean
theorem runFac_eq_factorial (n : Nat) : runFac n = some (Nat.factorial n) := by
```
```lean
#print axioms Wikifunctions.Python.runFac_eq_factorial
-- 'Wikifunctions.Python.runFac_eq_factorial' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
```

The specs are Mathlib's own `Nat.Coprime` and `Nat.factorial` — the repo defines no private gcd/factorial. Termination is proved (fuel `b+1` / `n+1` shown sufficient), so `= some …` rules out fuel exhaustion *in the model*. Scope caveat (SPEC_AUDIT D13): these theorems characterize *language semantics*; the live platform additionally bounds every execution (10¹⁰ wasm fuel, 9 s — pinned below), so large-`n` live factorial returns a resource error, not `n!`.

Check: `lake env lean Wikifunctions/Python/Z13701.lean && lake env lean Wikifunctions/Python/Z13667.lean`

### Trust anchors — how the one modelling assumption is discharged

The single assumption inherited by both theorems (`Imp.lean:29-37`): the `Imp` semantics faithfully models Python on this subset. Four artifacts attack it from different angles; every status below was reproduced on 2026-07-02 except where noted.

| Anchor | File | What it checks | Status (2026-07-02) |
|---|---|---|---|
| Cross-process difftest | `native/difftest.py` (chunked variant `native/difftest_chunked.py`) | the **compiled Lean embedding** (`diffdriver` binary, from `DiffDriver.lean` + `lakefile.toml:23-24`) vs the verbatim Z29182 Python (`difftest.py:16-19`) run in real CPython, 829 generated cases incl. 2⁴⁰-scale and worst-case pairs | **passes with a caveat (D10):** as committed it exits `FileNotFoundError` — `difftest.py:22` (and `difftest_chunked.py:13`) still compute `LEAN_DIR = ../lean`, a path stale since commit `4504464` flattened the repo. With `LEAN_DIR` pointed at the repo root: `cases: 829  mismatches: 0` (reproduced today). |
| In-process leanpy | `native/leanpy/Main.lean` | the **actual CPython interpreter**, dlopen'd into the Lean process via lean.py, called on the deployed sources (`Main.lean:20-25`) and compared to the spec `Nat.gcd a b == 1` / `fact` directly — no Lean-models-Python assumption at all | recorded pass: `tested 1607 cases, 0 mismatches` + `factorial: tested 21 cases (n=0..20), 0 mismatches` (`native/leanpy/README.md:18`, output format `Main.lean:55-69`). Not re-run today (isolated project; heavy Pantograph build, `.lake` gitignored). Caveats: `Main.lean:20-25` alpha-renames the parameters to `(a, b)`/`(n)` and re-indents — not byte-identical to the deployed source; int bridge is int64, cases ≤ 10⁶. |
| Dafny (SMT) | `native/Z13701_coprime.dfy` | a **re-implementation** of the same Euclid loop (`AreCoprime`, `:25-36`) verified against a recursive `Gcd` spec (`:15-19`) — cross-prover corroboration, *not* the deployed Python | re-verified today: `Dafny program verifier finished with 2 verified, 0 errors` (Dafny 4.11.0) |
| Verus (SMT, Rust) | `native/z13701_coprime.rs` | same algorithm in Rust (`are_coprime`, `:36-51`) against a `spec fn gcd` (`:19-23`) | re-verified today: `verification results:: 5 verified, 0 errors` (Verus 0.2026.06.14) |

Honesty notes: `native/README.md:6-11` itself flags that Dafny/Verus prove *re-implementations against transcribed specs* — a weaker claim than the Lean embedding, which proves the transcribed deployed source against Mathlib. And `native/README.md:37-82` describes a Verus artifact `rustpython_int_floordiv.rs` (grounding the `%` leaf in RustPython's real delegation chain) that is **absent from the repo** — only `z13701_coprime.rs` exists (SPEC_AUDIT D11).

- Check (difftest, D10 fix inlined): `lake build diffdriver && sed 's#"\.\.", "lean"#".."#' native/difftest.py > native/difftest_fixed.py && python3 native/difftest_fixed.py`
- Check (leanpy): `cd native/leanpy && lake build leanpycheck && LEANPY_LIBPYTHON=$(python3 -c "import sysconfig,os;print(os.path.join(sysconfig.get_config_var('LIBDIR'),'libpython'+sysconfig.get_config_var('VERSION')+'.dylib'))") ./.lake/build/bin/leanpycheck`
- Check (Dafny): `dafny verify native/Z13701_coprime.dfy`
- Check (Verus): `verus native/z13701_coprime.rs`

### Runtime pins — what actually executes this Python in production

The deployed executor is **not CPython**: user Python runs on **RustPython 0.5.0**, compiled to **wasm32-wasip1**, executed by **wasmtime 45** with fuel metering, inside the `function-evaluator` service (image `…/function-evaluator/rusty-py`, version `2026-06-30-213833` per the helm values below). Every cell links to a deployed source file; all URLs verified resolving 2026-07-02.

| Pin | Source (repo, file:line) | Verbatim core | Check |
|---|---|---|---|
| RustPython pinned **0.5.0**, target **wasm32-wasip1** | `function-evaluator` → `executors/wasm-utilities/build-rustpython-interpreter:12-14,42` | `# (T364563) Pinned to 0.5.0; …` / `git clone --depth 1 --branch 0.5.0 https://github.com/RustPython/RustPython.git` / `cargo build --release --target wasm32-wasip1 --features="freeze-stdlib"` | https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/executors/wasm-utilities/build-rustpython-interpreter |
| The `.wasm` is baked into the image | `function-evaluator` → `.pipeline/blubber.yaml:42-58` (variant `build-rustpython-interpreter`, `RUSTPYTHON_WASM: /srv/interpreters/rustpython.wasm`); prose in `interpreters/README.md` | `build-rustpython-interpreter:` … `RUSTPYTHON_WASM: /srv/interpreters/rustpython.wasm` | https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/interpreters/README.md |
| wasm host = **wasmtime 45.0.0** (WASI p1) | `function-evaluator` → `executor/Cargo.toml:19-20` | `wasmtime = { version = "45.0.0", features = [ "async" ] }` / `wasmtime-wasi = { version = "45.0.0", features = [ "p1" ] }` | https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/executor/Cargo.toml |
| Fuel metering is on; limit applied per store | `function-evaluator` → `executor/src/executor.rs:194,306,310` | `config.consume_fuel(true);` / `store.set_fuel(fuel_limit)?;` / `store.fuel_async_yield_interval(Some(10_000))?;` | https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/executor/src/executor.rs |
| Fuel default **10 000 000 000** (in code) | `function-evaluator` → `evaluator-layer/src/evaluator_service.rs:40-48` | `// Default to 10 billion fuel units. A trivial Python request consumes ~574M` … `.unwrap_or(10_000_000_000)` | https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/evaluator-layer/src/evaluator_service.rs |
| Interpreter file the evaluator loads | same file, `:73-76` | `PYTHON_INTERPRETER_FILE … unwrap_or_else(\|_\| "/srv/interpreter-rustpython.wasm".to_string())` | (same URL as above) |
| **Deployed** fuel = 10¹⁰, evaluator deadline = **9000 ms**, memory = 10 000 pages (640 MiB) | `operations/deployment-charts` (Gerrit; cited via the verified GitHub mirror `wikimedia/operations-deployment-charts`) → `helmfile.d/services/wikifunctions/values-python-evaluator.yaml:4-5,22,25-26` | `image: repos/abstract-wiki/wikifunctions/function-evaluator/rusty-py` / `FUNCTION_EVALUATOR_TIMEOUT_MS: "9000"` / `WASMTIME_FUEL_LIMIT: "10000000000"` / `WASMTIME_MEMORY_PAGES: "10000"` | https://raw.githubusercontent.com/wikimedia/operations-deployment-charts/master/helmfile.d/services/wikifunctions/values-python-evaluator.yaml |
| Orchestrator deadline = **9700 ms** | same repo → `values-main-orchestrator.yaml:38-41` | `# This should be a second or so larger than FUNCTION_EVALUATOR_TIMEOUT_MS` / `ORCHESTRATOR_TIMEOUT_MS: "9700"` | https://raw.githubusercontent.com/wikimedia/operations-deployment-charts/master/helmfile.d/services/wikifunctions/values-main-orchestrator.yaml |

Note the in-code timeout default is 30 000 ms (`evaluator_service.rs:23-31`); the 9 000 ms that actually binds in production comes from the helm values, which is why the helm file — not the Rust default — is the pin for the deadline.

**The honest gap (SPEC_AUDIT D11):** every trust note in this repo (`Imp.lean:31-37`, echoed at `Z13701.lean:37-39`, `Z13667.lean:41-43`, `native/difftest.py:5-9`) anchors faithfulness to **CPython**, and both empirical harnesses run CPython — but production runs RustPython 0.5.0 on wasm, as pinned above. The connecting lemma "RustPython ≡ CPython on this subset" (`while`/`!=`/`<=`/`%`/`*`/tuple assignment/`range` on non-negative ints) is version-stable core Python and holds on everything tested, but no in-repo Lean file mentions RustPython, and the one artifact that would certify a leaf of it (`rustpython_int_floordiv.rs`) is referenced by `native/README.md:37` yet not committed. A reviewer should treat that lemma as empirically supported, not discharged.

Check: `curl -s "https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/executors/wasm-utilities/build-rustpython-interpreter" | grep -n "branch 0.5.0"`

---

## The 25-function spec corpus — signatures and oracles against the live wiki (`WikifunctionsSpecs.lean`)

`WikifunctionsSpecs.lean` pins one Mathlib-backed oracle per addressable Wikifunction, in three trust tiers defined in its header (WikifunctionsSpecs.lean:13-22): **composite_provable** (ℕ/ℤ, in-kernel `decide`), **oracle_testable** (ℚ/ℤ/Float differential ground truth), **spec_only** (noncomputable ℝ). The table joins every block against the live wiki as fetched 2026-07-02: all 25 ZIDs exist with exactly these labels, arities, and argument/return types (SPEC_AUDIT.md §4 — zero drift). Type legend for the signature column, as returned live: `Z13518` = Natural number, `Z40` = Boolean, `Z6` = String, `Z16683` = Integer, `Z19677` = Rational number, `Z20838` = float64, `List(T)` = typed list `Z881(T)`, `Z1` = Object.

| ZID | Live label | Live signature | Lean spec decl | Tier claimed | Oracle | Status |
|---|---|---|---|---|---|---|
| [Z12427](https://www.wikifunctions.org/wiki/Z12427) | is prime | (Z13518) → Z40 | `Z12427_spec` WikifunctionsSpecs.lean:65 | composite_provable | `decide (Nat.Prime n)` | clean |
| [Z13612](https://www.wikifunctions.org/wiki/Z13612) | greatest common divisor | (Z13518, Z13518) → Z13518 | `Z13612_spec` WikifunctionsSpecs.lean:83 | composite_provable | `Nat.gcd` (corrects wrong_target `GCDMonoid`) | clean |
| [Z13660](https://www.wikifunctions.org/wiki/Z13660) | least common multiple | (Z13518, Z13518) → Z13518 | `Z13660_spec` WikifunctionsSpecs.lean:104 | composite_provable | `Nat.lcm` | clean |
| [Z13667](https://www.wikifunctions.org/wiki/Z13667) | factorial | (Z13518) → Z13518 | `Z13667_spec` WikifunctionsSpecs.lean:121 | composite_provable | `Nat.factorial` | clean |
| [Z13701](https://www.wikifunctions.org/wiki/Z13701) | are coprime (natural numbers) | (Z13518, Z13518) → Z40 | `Z13701_spec` WikifunctionsSpecs.lean:145 | composite_provable | `decide (Nat.Coprime m n)` | clean |
| [Z13822](https://www.wikifunctions.org/wiki/Z13822) | modular multiplicative inverse | (Z13518, Z13518) → Z13518 | `Z13822_spec` WikifunctionsSpecs.lean:164 | composite_provable | `((a : ZMod n)⁻¹).val` | clean |
| [Z13835](https://www.wikifunctions.org/wiki/Z13835) | nth Fibonacci number | (Z13518) → Z13518 | `Z13835_spec` WikifunctionsSpecs.lean:194 | composite_provable | `Nat.fib` | clean |
| [Z13955](https://www.wikifunctions.org/wiki/Z13955) | Euler totient function | (Z13518) → Z13518 | `Z13955_spec` WikifunctionsSpecs.lean:210 | composite_provable | `Nat.totient` | clean |
| [Z14933](https://www.wikifunctions.org/wiki/Z14933) | is perfect number | (Z13518) → Z40 | `Z14933_spec` WikifunctionsSpecs.lean:234 | composite_provable | `decide (Nat.Perfect n)` | clean |
| [Z18194](https://www.wikifunctions.org/wiki/Z18194) | powerset | (List(Z1)) → List(List(Z1)) | `Z18194_spec` WikifunctionsSpecs.lean:256 | composite_provable | `Finset.powerset` (tagged representation_mismatch: Finset vs live list-with-duplicates) | clean |
| [Z13521](https://www.wikifunctions.org/wiki/Z13521) | add two Natural numbers | (Z13518, Z13518) → Z13518 | `Z13521_spec` WikifunctionsSpecs.lean:285 | composite_provable | `a + b` on ℕ (= `Nat.add`) | clean |
| [Z15483](https://www.wikifunctions.org/wiki/Z15483) | nth r-simplex number | (Z13518, Z13518) → Z13518 | `Z15483_spec` WikifunctionsSpecs.lean:304 | composite_provable | `Nat.choose (n + r - 1) r` | clean |
| [Z15849](https://www.wikifunctions.org/wiki/Z15849) | Kronecker delta | (Z13518, Z13518) → Z13518 | `Z15849_spec` WikifunctionsSpecs.lean:322 | composite_provable | `if i = j then 1 else 0` | clean |
| [Z20000](https://www.wikifunctions.org/wiki/Z20000) | Bayes' theorem conditional probability P(A\|B) | (Z19677, Z19677, Z19677) → Z19677 | `Z20000_spec` WikifunctionsSpecs.lean:343 | composite_provable | `pBA * pA / pB` on ℚ | **flagged D18** — ℚ oracle sits in the in-kernel ℕ/ℤ tier (its own check at :353 needs `norm_num`, not `decide`); belongs in tier 2, plus undocumented pB = 0 totalization |
| [Z28925](https://www.wikifunctions.org/wiki/Z28925) | is Pythagorean triple | (Z13518, Z13518, Z13518) → Z40 | `Z28925_spec` WikifunctionsSpecs.lean:362 | composite_provable | `decide (a*a + b*b = c*c)` | **flagged D1** — order-sensitive spec mis-tagged `[faithful]`: on (5,4,3) Lean = `false`, both live impls (Z35061 sorts, Z28926 swaps max into K3) = `True` |
| [Z30840](https://www.wikifunctions.org/wiki/Z30840) | arithmetic mean of Natural numbers as Rational | (List(Z13518)) → Z19677 | `Z30840.spec` WikifunctionsSpecs.lean:397 | oracle_testable | list sum / length over ℚ (empty-list convention documented) | clean |
| [Z10862](https://www.wikifunctions.org/wiki/Z10862) | (!) multiply two numeric strings (full stop input/output format) | (Z6, Z6) → Z6 | `Z10862_spec` WikifunctionsSpecs.lean:434 | oracle_testable | `a * b` on ℤ (ℚ variant :443) | **flagged D2** — exact ℤ/ℚ oracle vs float64-lossy live impls: live "0.1"×"0.2" → `"0.020000000000000004"`, live Python renders `'%g'` (6 sig. digits) |
| [Z21917](https://www.wikifunctions.org/wiki/Z21917) | complex conjugate (integer list) | (Z16683, Z16683) → List(Z16683) | `Z21917_spec` WikifunctionsSpecs.lean:455 | oracle_testable | `(a, -b)` on ℤ×ℤ (tagged representation_mismatch: paired vs curried) | clean |
| [Z31173](https://www.wikifunctions.org/wiki/Z31173) | Euler characteristic of polyhedron | (Z13518, Z13518, Z13518) → Z16683 | `Z31173_spec` WikifunctionsSpecs.lean:479 | oracle_testable | `(V : ℤ) − E + F` (ℤ return matches live Z16683) | clean |
| [Z21003](https://www.wikifunctions.org/wiki/Z21003) | natural logarithm (float64) | (Z20838) → Z20838 | `Z21003_spec` WikifunctionsSpecs.lean:496 | oracle_testable | `Float.log` (ideal `Real.log` :504) | clean |
| [Z21005](https://www.wikifunctions.org/wiki/Z21005) | float64 logarithm base 10 | (Z20838) → Z20838 | `Z21005_spec` WikifunctionsSpecs.lean:523 | oracle_testable | `Float.log x / Float.log 10.0` (ideal `Real.logb 10` :530) | **flagged D8** — live impls call native `log10`: at x = 1000 native gives exactly `3.0`, oracle gives `2.9999999999999996`; the header's "bit-for-bit" claim overreaches (≤ 1–2 ULP is honest) |
| [Z12665](https://www.wikifunctions.org/wiki/Z12665) | exponentiation | (Z20838, Z20838) → Z20838 | `Z12665_spec` WikifunctionsSpecs.lean:550 | oracle_testable | Float `x ^ y` (ideal `Real.rpow` :557) | clean |
| [Z13341](https://www.wikifunctions.org/wiki/Z13341) | linear interpolation | (Z20838, Z20838, Z20838) → Z20838 | `Z13341_spec` WikifunctionsSpecs.lean:576 | oracle_testable | `(1.0 − t) * a + t * b` (ideal `AffineMap.lineMap` :584) | **flagged D7** — live Python impl Z13342 returns an error for t ∉ [0,1]; the bit-exactness claim holds only against Z31184 (JS) and Z34167 (composite) |
| [Z35278](https://www.wikifunctions.org/wiki/Z35278) | Shannon entropy from string | (Z6) → Z20838 | `Z35278.Z35278_spec` WikifunctionsSpecs.lean:623 | oracle_testable | fold of `−p · log₂ p` over the char distribution (nats/bits ideals :639/:643 via `Real.negMulLog`) | clean |
| [Z16483](https://www.wikifunctions.org/wiki/Z16483) | (!) gamma function (strings) | (Z6) → Z6 | `Z16483_spec` WikifunctionsSpecs.lean:673 | spec_only | `Real.Gamma` (noncomputable; Γ(n+1) = n! pinned :680) | clean |

The 20 "clean" rows carry only info-level notes in SPEC_AUDIT.md §5 (e.g. Z14933's untested n = 0 composite edge, Z16483's live impl being float64 `math.gamma` rather than arbitrary precision); the five marked rows are SPEC_AUDIT.md §3 findings D1, D2, D7, D8, D18.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z12427|Z13612|Z13660|Z13667|Z13701|Z13822|Z13835|Z13955|Z14933|Z18194|Z13521|Z15483|Z15849|Z20000|Z28925|Z30840|Z10862|Z21917|Z31173|Z21003|Z21005|Z12665|Z13341|Z35278|Z16483"` — returns all 25 rows in one response (each `wikilambda_fetch` field is a JSON-encoded string; parse it, then read the label from `Z2K3.Z12K1[]` where `Z11K1 = "Z1002"` and the signature from `Z2K2.Z8K1[].Z17K1` / `Z2K2.Z8K2`).

### The four community type pins

Every signature above bottoms out in four community-defined types. These are wiki content, not schemata (SPEC_AUDIT.md §1, layer 3) — only a live fetch pins them. Key structures below are quoted verbatim from the 2026-07-02 fetch (`Z2K2.Z4K2`, each key's multilingual `Z3K3` collapsed to its English string).

**Z13518 — "Natural number"** (carrier of `Val.nat`/ℕ across the corpus): a single key holding a decimal string, hence arbitrary precision — ℕ is the right Lean carrier, no overflow gap.

```json
{"Z1K1": "Z3", "Z3K1": "Z6", "Z3K2": "Z13518K1", "Z3K3(en)": "value"}
```
Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z13518"`

**Z16683 — "Integer"** (return type of Z31173, argument type of Z21917): sign + magnitude.

```json
{"Z1K1": "Z3", "Z3K1": "Z16659", "Z3K2": "Z16683K1", "Z3K3(en)": "sign"}
{"Z1K1": "Z3", "Z3K1": "Z13518", "Z3K2": "Z16683K2", "Z3K3(en)": "absolute value"}
```
Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z16683"`

**Z19677 — "Rational number"** (Z20000's argument/return type; the Lean carrier is ℚ, i.e. this record up to fraction equality — the type the retired citation "Z70" in WikifunctionsEval.lean:18 should name, finding D14):

```json
{"Z1K1": "Z3", "Z3K1": "Z16659", "Z3K2": "Z19677K1", "Z3K3(en)": "sign"}
{"Z1K1": "Z3", "Z3K1": "Z13518", "Z3K2": "Z19677K2", "Z3K3(en)": "numerator"}
{"Z1K1": "Z3", "Z3K1": "Z13518", "Z3K2": "Z19677K3", "Z3K3(en)": "denominator"}
```
Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z19677"`

**Z20838 — "float64"** (carrier of every tier-2 Float block): a field-level IEEE-754 binary64 encoding — sign, exponent, fractional significand, plus a special-value slot (Z20825) for NaN/±Inf:

```json
{"Z1K1": "Z3", "Z3K1": "Z16659", "Z3K2": "Z20838K1", "Z3K3(en)": "sign"}
{"Z1K1": "Z3", "Z3K1": "Z16683", "Z3K2": "Z20838K2", "Z3K3(en)": "exponent"}
{"Z1K1": "Z3", "Z3K1": "Z13518", "Z3K2": "Z20838K3", "Z3K3(en)": "significand (fractional part)"}
{"Z1K1": "Z3", "Z3K1": "Z20825", "Z3K2": "Z20838K4", "Z3K3(en)": "special value"}
```
Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z20838"`

### The Float claim

The tier-2 header (WikifunctionsSpecs.lean:17-19) rests on one identification: Lean `Float` **is** IEEE-754 binary64, the same format Z20838 encodes field-by-field (above) and that live implementations manipulate as JS `Number` / Python `float`. The Lean side is pinned by the compiler itself — this repo's toolchain is `leanprover/lean4:v4.32.0-rc1` (lean-toolchain:1), whose core source states verbatim: "`Float` corresponds to the IEEE 754 *binary64* format (`double` in C or `f64` in Rust)" ([src/Init/Data/Float.lean#L34](https://github.com/leanprover/lean4/blob/v4.32.0-rc1/src/Init/Data/Float.lean#L34), `structure Float` at L48; arithmetic is `@[extern]` to C `double`/libm). Bit-equality — not mere approximation — is checked through the one corpus function whose body is pure binary64 arithmetic with no transcendental call, Z13341 lerp. Lean (WikifunctionsSpecs.lean:576,579) vs the live first-listed implementation [Z31184](https://www.wikifunctions.org/wiki/Z31184) (i.e. what production's `FirstImplementationSelector` runs):

```lean
-- WikifunctionsSpecs.lean:576,579
def Z13341_spec (a b t : Float) : Float := (1.0 - t) * a + t * b
#guard Z13341_spec 10.0 20.0 0.25 == 12.5
```
```javascript
// live Z31184.Z2K2.Z14K3.Z16K2 (JavaScript, Z16K1 = Z600)
function Z13341( Z13341K1, Z13341K2, Z13341K3 ) {
	return Z13341K1 * (1 - Z13341K3) + Z13341K2 * Z13341K3;
}
```

The two expressions differ only by the order of each multiplication's operands, and IEEE-754 multiplication is commutative, so on representable inputs the outputs are bit-identical (SPEC_AUDIT.md §4, "bit-identical to JS by commutativity of float multiply") — this is what licenses `#eval`-level differential testing for the rest of tier 2, with the honest caveat that transcendental blocks (Z21003, and especially Z21005/D8) are libm-dependent and only ULP-close.

Check: `curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=Z31184" && curl -s "https://raw.githubusercontent.com/leanprover/lean4/v4.32.0-rc1/src/Init/Data/Float.lean" | sed -n '34p'`

---

## Reproducing every citation

Every `Check:` command and Check-column link above, deduplicated (zid sets that are subsets of a larger fetch are folded in — e.g. `Z13702`, `Z13548`, and the solo `Z29182`/`Z13668` fetches). The per-section Check lines add `jq`/`python3` filters that select the exact cited field; the base commands below fetch everything those filters read, so running this list top to bottom re-verifies the whole blueprint.

### Live API curls

All ZObject fetches share one shape — substitute each `<ZIDS>` set below:

```
curl -s "https://www.wikifunctions.org/w/api.php?action=wikilambda_fetch&format=json&zids=<ZIDS>"
```

- Composite functions + transcribed impls: `Z13701|Z13702` · `Z13660|Z13661` · `Z15849|Z15852` · `Z15483|Z15487` · `Z20000|Z20001` · `Z14933|Z14934`
- Leaf functions + realizing impls: `Z13522|Z13533` · `Z13612|Z13642` · `Z13539|Z13540` · `Z13546|Z13548` · `Z13521|Z13573` · `Z13582|Z13586` · `Z13846|Z13847` · `Z13848|Z14852` · `Z13993|Z13994` · `Z19706|Z20036` · `Z19708|Z20037`
- ÷0 guard sources (D3/D4): `Z20037|Z19710` (D3's `Z13548` is covered by `Z13546|Z13548` above)
- Imperative-Python impl sources: `Z29182|Z13668`
- Community type pins: `Z13518` · `Z41|Z42` · `Z16683` · `Z19677` · `Z20838`
- Float-claim impl: `Z31184`
- The whole 25-function corpus in one call: `Z12427|Z13612|Z13660|Z13667|Z13701|Z13822|Z13835|Z13955|Z14933|Z18194|Z13521|Z15483|Z15849|Z20000|Z28925|Z30840|Z10862|Z21917|Z31173|Z21003|Z21005|Z12665|Z13341|Z35278|Z16483`

Plus the one non-fetch API call (live error envelope, abstraction B):

```
curl -s "https://www.wikifunctions.org/w/api.php" --data-urlencode "action=wikifunctions_run" --data-urlencode "format=json" --data-urlencode 'function_call={"Z1K1":"Z7","Z7K1":"Z13546","Z13546K1":{"Z1K1":"Z13518","Z13518K1":"1"},"Z13546K2":{"Z1K1":"Z13518","Z13518K1":"0"}}'
```

### Schemata and deployed-source raw URLs

function-schemata, root `https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/raw/main/data/CANONICAL/`:

- `Z1.yaml` · `Z2.yaml` · `Z7.yaml` · `Z8.yaml` · `Z9.yaml` · `Z14.yaml` · `Z18.yaml` · `Z40.yaml` · `RESOLVER.yaml`

function-orchestrator, root `https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-orchestrator/-/raw/main/`:

- `src/transpilation/utils.js` (lazy table, `sed -n '1,11p'`; also `grep`-check `branch 0.5.0` style line pins)
- `src/implementationSelector.js` (`sed -n '44,56p'`)

function-evaluator, root `https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-evaluator/-/raw/main/`:

- `executors/wasm-utilities/build-rustpython-interpreter` (verify with `| grep -n "branch 0.5.0"`)
- `interpreters/README.md`
- `executor/Cargo.toml`
- `executor/src/executor.rs`
- `evaluator-layer/src/evaluator_service.rs`

Deployment charts (GitHub mirror), root `https://raw.githubusercontent.com/wikimedia/operations-deployment-charts/master/helmfile.d/services/wikifunctions/`:

- `values-python-evaluator.yaml`
- `values-main-orchestrator.yaml`

Lean core (Float = binary64 pin):

- `https://raw.githubusercontent.com/leanprover/lean4/v4.32.0-rc1/src/Init/Data/Float.lean` (`| sed -n '34p'`)

### Spec page

- `https://www.wikifunctions.org/wiki/Wikifunctions:Function_model` — anchors cited: `#Z9/References`, `#Z4/Types`, `#Composition`, `#Z7/Function_calls`, `#Z8/Functions`, `#Persistent_and_transient`, `#Example_evaluation`, `#Evaluation_order`, `#Z22/Evaluation_result`, `#Z881/Typed_lists`
- Anchor existence check: `curl -s "https://www.wikifunctions.org/w/api.php?action=parse&format=json&page=Wikifunctions:Function_model&prop=sections" | jq -r '.parse.sections[].anchor'`

### Repo files (local; repo root, branch `spec-audit` @ `778a3e0`)

- Core lines: `sed -n '16p;20,24p;28,31p;34p;38p;40,51p' Wikifunctions/Core.lean`
- Re-elaborate the two main theorems: `lake env lean Wikifunctions/Python/Z13701.lean && lake env lean Wikifunctions/Python/Z13667.lean`
- Difftest (D10 fix inlined): `lake build diffdriver && sed 's#"\.\.", "lean"#".."#' native/difftest.py > native/difftest_fixed.py && python3 native/difftest_fixed.py`
- leanpy: `cd native/leanpy && lake build leanpycheck && LEANPY_LIBPYTHON=$(python3 -c "import sysconfig,os;print(os.path.join(sysconfig.get_config_var('LIBDIR'),'libpython'+sysconfig.get_config_var('VERSION')+'.dylib'))") ./.lake/build/bin/leanpycheck`
- Dafny: `dafny verify native/Z13701_coprime.dfy`
- Verus: `verus native/z13701_coprime.rs`