module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.DiagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


/-- **The decidable witness relation underlying `DiagFixed`'s r.e.-ness, extracted.** Unfolding
`REPred`'s own definition (`p n ↔ ∃ i, q ⟨i,n⟩` with `q` recursively decidable via a `{0,1}`-valued
primitive-recursive `qChar`) exposes `qChar` directly: `DiagFixed P a n ↔ ∃ i, qChar ⟨i,n⟩ = 1`.
This is the "genuinely decidable, no unbounded search" ingredient that Theorem 8.8(c) Parts 2–4 gate
their primitive-recursive fold on. -/
theorem diagFixed_exists_qChar {P : ComputablePresentation V} {a : ApproximableMap V V}
    (ha : ComputableMap P P a) :
    ∃ qChar : ℕ → ℕ, Nat.Primrec qChar ∧
      ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1 := by
  obtain ⟨q, hq, hqe⟩ := diagFixed_isREPred ha
  obtain ⟨f, hf, hfe⟩ := hq
  exact ⟨f, hf, fun n => (hqe n).trans (exists_congr (fun i => hfe _))⟩

end DomainTheory.NeighbourhoodSystems
