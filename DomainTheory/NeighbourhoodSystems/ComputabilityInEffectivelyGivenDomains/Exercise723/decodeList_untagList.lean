module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagState_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **`decodeList (untagList c) = (untagRef c).1`.** The `appendCode`-reversal in `untagList`
undoes the reversal built up by `untagStep`'s accumulator. -/
theorem decodeList_untagList (c : ℕ) : decodeList (untagList c) = (untagRef c).1 := by
  unfold untagList
  rw [decodeList_appendCode, decodeList_zero, List.append_nil]
  have hspec := untagState_spec c
  have hrevAcc : (untagState c).unpair.2.unpair.2.unpair.1
      = (untagRef c).1.foldl (fun acc x => Nat.pair x acc + 1) 0 := by
    rw [hspec]; simp only [unpair_pair_snd, unpair_pair_fst]
  rw [hrevAcc]
  have hfold : ∀ l : List ℕ, ∀ r : ℕ,
      decodeList (l.foldl (fun acc x => Nat.pair x acc + 1) r) = l.reverse ++ decodeList r := by
    intro l
    induction l with
    | nil => intro r; simp
    | cons a l ih =>
      intro r
      rw [List.foldl_cons, ih, decodeList_succ, unpair_pair_fst, unpair_pair_snd,
        List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [hfold (untagRef c).1 0, decodeList_zero, List.append_nil, List.reverse_reverse]

end DomainTheory.NeighbourhoodSystems.Exercise723
