/-ai
This file assembles Factoid 8.2, the lambda-calculus model in which D is congruent to A plus the function space from D to D. Consistency and the token carrier are developed by well-founded depth, entailment is the inductive depth relation of Scott's clauses (8) through (11), and the lambda system is the information system of well-formed tokens, with the domain equation through the unfolding into the sum of A and the function space.

A raw token lies in the fold, from the empty finset, of forgetful insertion along a multiset of lambda tokens if and only if it is the underlying token of some element of that multiset.

The proof inducts on the multiset. Both sides fail for the empty multiset. For a cons cell, membership in the inserted fold is the value of the head or membership in the fold of the tail, and the inductive hypothesis matches the tail with the tail of the multiset.

The union of a finset u with the insertion of a token a into a finset t equals the insertion of a into the union of u and t.

By extensionality, an element of the left side lies in u, hence in the inserted union, or in the insertion, hence equals a or lies in t, and both of those lie in the inserted union. An element of the right side equals a, hence lies in the inserted right-hand summand, or lies in the union, hence lies in u or in t, and both of those lie in the left side.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamForget
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamForgetInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamTokenCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntN
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamTokenEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForget
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lambdaSystem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamUnfold
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamRhs
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamAtomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_singleton_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_singleton_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_nonempty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_con
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_fun
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.funion_empty_right_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.insert_filter_ne_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.filter_ne_subset_of_subset_insert_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_funion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_insert_le
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_funion_of_entSet
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.funion_assoc_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.funion_comm_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_funion_le
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_insert_of_ent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_trans
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_foldr_lamDForget
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_subset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_insert_of_ent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt_trans
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForget_listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamForgetInsert

@[expose] public section

/-!
# Factoid 8.2 — λ-calculus model `D ≅ A + (D → D)`

**Scott 1982, §8.** `D` and `Con_D` are mutually recursive. Lean rejects putting the
FunCon-style clause (7) inside an inductive (negative occurrence), so the primary
path uses well-founded **`LamConDepth`** (`termination_by finsetMaxDepth`) and
inductive **`LamEntDepth`** (Scott (8)–(11)). Staged `LamConN` / early `LamToken`
remain scaffolding only.

**Status:** Def 2.1 packaged as `lambdaSystem` on `LamDToken` (depth WF); domain
equation via `lamUnfold` / `lamRhs` into `sumSystem A (functionSystem D D)`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

/-! ## Raw tokens + decidable equality -/

/-! ## Projections -/


/-! ## Staged consistency -/

variable (A : InfoSys α)


theorem mem_foldr_lamForget (s : Multiset (LamToken A)) (t : RawLamToken α) :
    t ∈ Multiset.foldr (lamForgetInsert (A := A)) ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, lamForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩


/-! ## Staged entailment (Scott (8)–(11)) — definitions only

Full `ent_refl` / `ent_con` / `ent_trans` for the `InfoSys` instance remain; the
definitions below package Scott’s clauses (8)–(11) at stages matching `LamConN`.
-/


/-! ## Inversion lemmas for staged Con -/


/-! ## ent_con: inserting an entailed token preserves consistency -/


/-! ## Depth-based entailment (Scott (8)–(11), inductive FunEnt-style) -/


/-! ### Funion / filter helpers + weaken_insert + funion_of_entSet + insert_of_ent -/


theorem funion_insert_lam (u : Finset (RawLamToken α)) (a : RawLamToken α)
    (t : Finset (RawLamToken α)) : u ∪' insert a t = insert a (u ∪' t) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with hu | hins
    · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inl hu))
    · rcases Finset.mem_insert.mp hins with ha | ht
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inr ht))
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | h
    · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl ha)))
    · rcases mem_funion.mp h with hu | ht
      · exact mem_funion.mpr (Or.inl hu)
      · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ht)))


/-! ### Scott (8)–(11): `ent_trans` (Def 2.1) -/


/-! ### Phase B — `lambdaSystem` (Def 2.1) on `LamConDepth` -/


/-! ### Phase C — domain equation `D ≅ A + (D → D)` -/


end InfoSys
end DomainTheory.InformationSystems
