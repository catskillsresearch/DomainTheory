/-ai
Adding a function-space token entailed by a consistent set preserves consistency of the insertion.

Let t be a subset of the insertion whose input union is consistent. If the entailed token lies in t, delete it to obtain a subset of the original set, and rewrite the input hypothesis as consistency of the union of that token's input with the remaining input union. The entailment supplies a subset of the original set. The union of that subset with the remainder stays inside the original set, and extending the input entailment from the token's input to the larger input makes the combined input union consistent. Consistency of the original set gives consistency of the corresponding output union. Pushing the output entailment of the token across that union shows that the union of the token's output with the remaining output union is consistent, which is the output union of t. If the entailed token does not lie in t, then t is already a subset of the original set, and consistency applies directly.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_assoc
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_comm
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_assoc'
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_comm'
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_insert
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion_insert
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.entSet_inputUnion_of_ent
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.insert_filter_ne
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.filter_ne_subset_of_subset_insert

public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_v
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Adding an entailed function-space token preserves consistency. -/
theorem functionSystem_ent_con {w : Finset (FunToken A B)} {p : FunToken A B}
    (hEnt : FunEnt A B w p) : FunCon A B (insert p w) := by
  obtain ⟨hw, s, hs, hEntIn, hEntOut⟩ := hEnt
  intro t ht hin
  if hp : p ∈ t then
    let t' := t.filter (· ≠ p)
    have ht_eq : insert p t' = t := insert_filter_ne A B hp
    have ht'sub : t' ⊆ w := filter_ne_subset_of_subset_insert A B ht
    have hin' : p.val.1 ∪' funInputUnion A B t' ∈ A.Con := by
      rwa [← ht_eq, funInputUnion_insert] at hin
    have hsub : s ∪' t' ⊆ w := funion_subset_iff.mpr ⟨hs, ht'sub⟩
    have hEnt_in_s : A.EntSet p.val.1 (funInputUnion A B s) :=
      entSet_inputUnion_of_ent A B hEntIn
    have hEnt_big : A.EntSet (p.val.1 ∪' funInputUnion A B t') (funInputUnion A B s) :=
      proposition_2_3_v A p.property.1 hin' (subset_funion_left _ _) hEnt_in_s
        (Finset.Subset.refl _)
    have hbig : (p.val.1 ∪' funInputUnion A B t') ∪' funInputUnion A B s ∈ A.Con :=
      proposition_2_3_ii A hin' hEnt_big
    have hin_st' : funInputUnion A B s ∪' funInputUnion A B t' ∈ A.Con := by
      have heq :
          (p.val.1 ∪' funInputUnion A B t') ∪' funInputUnion A B s =
            p.val.1 ∪' (funInputUnion A B s ∪' funInputUnion A B t') := by
        rw [funion_assoc, funion_comm (funInputUnion A B t')]
      have hbig' : p.val.1 ∪' (funInputUnion A B s ∪' funInputUnion A B t') ∈ A.Con := by
        rwa [heq] at hbig
      exact A.con_subset hbig' (subset_funion_right _ _)
    have hin_union : funInputUnion A B (s ∪' t') ∈ A.Con := by
      rwa [funInputUnion_funion]
    have hout_union : funOutputUnion A B s ∪' funOutputUnion A B t' ∈ B.Con := by
      have : funOutputUnion A B (s ∪' t') ∈ B.Con := hw _ hsub hin_union
      rwa [funOutputUnion_funion] at this
    have hout_s : funOutputUnion A B s ∈ B.Con :=
      B.con_subset hout_union (subset_funion_left _ _)
    have hEnt_out' : B.EntSet (funOutputUnion A B s ∪' funOutputUnion A B t') p.val.2 :=
      proposition_2_3_v B hout_s hout_union (subset_funion_left _ _) hEntOut
        (Finset.Subset.refl _)
    have hfinal :
        (funOutputUnion A B s ∪' funOutputUnion A B t') ∪' p.val.2 ∈ B.Con :=
      proposition_2_3_ii B hout_union hEnt_out'
    have hout_t : p.val.2 ∪' funOutputUnion A B t' ∈ B.Con := by
      have heq :
          (funOutputUnion A B s ∪' funOutputUnion A B t') ∪' p.val.2 =
            funOutputUnion A B s ∪' (p.val.2 ∪' funOutputUnion A B t') := by
        rw [funion_assoc', funion_comm' (funOutputUnion A B t')]
      have hfinal' :
          funOutputUnion A B s ∪' (p.val.2 ∪' funOutputUnion A B t') ∈ B.Con := by
        rwa [heq] at hfinal
      exact B.con_subset hfinal' (subset_funion_right _ _)
    have : funOutputUnion A B t ∈ B.Con := by
      rwa [← ht_eq, funOutputUnion_insert]
    exact this
  else
    have ht' : t ⊆ w := by
      intro q hq
      have : q ∈ insert p w := ht hq
      rcases Finset.mem_insert.mp this with rfl | hqW
      · exact False.elim (hp hq)
      · exact hqW
    exact hw t ht' hin

end InfoSys

end DomainTheory.InformationSystems
