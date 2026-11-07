module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.D_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixedNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

theorem fixedNbhd_isEffectivelyGiven {P : ComputablePresentation V} {a : ApproximableMap V V}
    (hcomp : ComputableMap P P a) : (fixedNbhd a).IsEffectivelyGiven := by
  obtain ⟨qChar, hqCharp, hqChar⟩ := diagFixed_exists_qChar hcomp
  obtain ⟨cons, hconsp, hconse⟩ := P.cons_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have h := hconse (Nat.pair n m)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    exact h.symm
  refine ⟨{
    X := D_X P qChar cons
    mem_X := D_X_mem hqChar hcons
    surj := fun hY => D_X_surj hqChar hcons hY
    interEq_computable := D_X_interEq_computable P qChar cons hqCharp hconsp
    cons_computable := D_X_cons_computable P qChar cons hqChar hcons hqCharp hconsp
    inter := D_inter
    inter_primrec := D_inter_primrec
    inter_spec := fun h => D_X_inter_spec hcons h
    masterIdx := 0
    masterIdx_spec := ?_ }⟩
  show D_X P qChar cons 0 = V.master
  show P.X (myFoldCode P qChar cons 0) = V.master
  rw [myFoldCode_eq, decodeList_zero, myFold_nil, P.masterIdx_spec]

end DomainTheory.NeighbourhoodSystems
