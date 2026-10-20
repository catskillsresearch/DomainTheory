module


public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

/-- **Definition 7.1 (Scott 1981, PRG-19).** A *computable presentation* of a neighbourhood system
`V` over a token type `α`: an enumeration `X : ℕ → Set α` whose range is exactly `𝒟` (`mem_X` and
`surj`), such that Scott's two relations on the integer indices are recursively decidable:

* `interEq_computable` is (i): the ternary relation `Xₙ ∩ Xₘ = X_k`;
* `cons_computable` is (ii): the binary consistency relation `∃ k. X_k ⊆ Xₙ ∩ Xₘ`
  (Scott's `X_k ⊆ Xₙ and X_k ⊆ Xₘ`).

Only the enumeration `X` is data; the remaining fields are `Prop`s, so a presentation is built
choice-free. -/
structure ComputablePresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`: every neighbourhood appears as some `Xₙ`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(i)** — `Xₙ ∩ Xₘ = X_k` is recursively decidable in `n, m, k`. -/
  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)
  /-- **7.1(ii)** — consistency `∃ k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable in `n, m`. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)
  /-- A **primitive-recursive intersection function**: an index of `Xₙ ∩ Xₘ` whenever that
  intersection is a neighbourhood (i.e. consistent). This makes explicit the operation that 7.1(i)
  is *about*: in Scott's general-recursive reading of "recursively decidable" the index can be
  recovered from `interEq_computable` by an (unbounded) search `μk. Xₙ ∩ Xₘ = X_k`, but that search
  is not *primitive* recursive; for the function-space presentation (Theorem 7.5) we need to
  *form* component intersections primitively, so we carry the function as part of the data of an
  ("acceptable") computable presentation. Off the consistent domain `inter n m` may be junk. -/
  inter : ℕ → ℕ → ℕ
  /-- The intersection function is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  inter_primrec : Nat.Primrec (fun t => inter t.unpair.1 t.unpair.2)
  /-- `inter n m` indexes `Xₙ ∩ Xₘ` whenever that intersection is consistent. -/
  inter_spec : ∀ {n m : ℕ}, (∃ k, X k ⊆ X n ∩ X m) → X (inter n m) = X n ∩ X m
  /-- A fixed index of the master neighbourhood `Δ` (used to seed finite intersections). -/
  masterIdx : ℕ
  /-- `X masterIdx = Δ`. -/
  masterIdx_spec : X masterIdx = V.master

end DomainTheory.NeighbourhoodSystems
