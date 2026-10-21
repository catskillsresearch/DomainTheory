/-ai
The predicate of a code that packages a witness index, an enumeration index, and a step, asserting that the enumerated neighbourhood is contained in the enumerated neighbourhood of the witness paired with itself and that the two presented neighbourhoods of the step bracket the witness, is recursively decidable.

The witness index, the enumeration index, and the two halves of the step are primitive recursive, as is the code of the witness paired with itself. Each of the three inclusions is decided by composing the corresponding inclusion character with the pairing of those projections, and the three decidable predicates are conjoined.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)


/-- **The per-witness `sub`-step predicate is recursively decidable**, coded as a function of
`w = ⟨y, ⟨n, e⟩⟩`: the function-space inclusion `Xenum n ⊆ Xenum (codePair y y)` (via `fincl`, the
function-space presentation's own inclusion char) conjoined with the two `𝒟`-inclusions bracketing
`y` (via `incl`, `P`'s own inclusion char). -/
theorem subStep_recDecidable (fincl incl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2)
    (hfinclp : Nat.Primrec fincl)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl) :
    RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1) ∧
        P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1 ∧
          P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he1 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hcodeYY : Nat.Primrec (fun w : ℕ => codePair w.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hy.pair hy).pair (Nat.Primrec.const 0))
  have h1 : RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1)) :=
    ⟨fun w => fincl (Nat.pair w.unpair.2.unpair.1 (codePair w.unpair.1 w.unpair.1)),
      hfinclp.comp (hn.pair hcodeYY), fun w => by
        rw [hfincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h2 : RecDecidable (fun w : ℕ => P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1) :=
    ⟨fun w => incl (Nat.pair w.unpair.2.unpair.2.unpair.1 w.unpair.1), hinclp.comp (he1.pair hy),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h3 : RecDecidable (fun w : ℕ => P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) :=
    ⟨fun w => incl (Nat.pair w.unpair.1 w.unpair.2.unpair.2.unpair.2), hinclp.comp (hy.pair he2),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  exact h1.and (h2.and h3)

end SubComputable
end DomainTheory.NeighbourhoodSystems
