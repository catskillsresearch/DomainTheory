/-ai
The reference decoder is a right inverse of tag. Tag of its list component at its value component returns the original code.

The proof is strong induction on the code, in the pattern of the surjectivity of tag. If the first component of the numeral decoding is zero, the zero case of the decoder and the pairing equation for numerals reduce the claim, after the empty-list equation for tag, to the round trip of the numeral coding. If that first component is a successor, the successor case of the decoder applies. The pairing equation recovers the code as the numeral of that successor and the second component, and the successor bound on numerals makes the second component strictly smaller. The cons equation for tag, the inductive hypothesis, and that recovery close the step.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagRef_zero_case
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagRef_succ_case

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



























































/-- **`untagRef` is a genuine right-inverse of `tag`.** Strong induction on `c`, mirroring
`tag_surjective`. -/
theorem tag_untagRef (c : ℕ) : tag (untagRef c).1 (untagRef c).2 = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases hc : (unnum c).1 with a | k
    · rw [untagRef_zero_case hc]
      have heq := numP_unnum c
      simp only [numP, hc] at heq
      rw [tag_nil]
      exact heq
    · rw [untagRef_succ_case hc]
      have heq : num (k + 1) (unnum c).2 = c := by
        have h := numP_unnum c
        simpa [numP, hc] using h
      have hlt : (unnum c).2 < c := by
        have hb := num_succ_left_gt k (unnum c).2
        omega
      rw [tag_cons, ih (unnum c).2 hlt, heq]

end DomainTheory.NeighbourhoodSystems.Exercise723
