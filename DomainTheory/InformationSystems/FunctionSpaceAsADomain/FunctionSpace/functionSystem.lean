module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.exists_combined_witness
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.filter_ne_subset_of_subset_insert
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_assoc
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_assoc'
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_comm
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funion_comm'
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.insert_filter_ne
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iv
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_v

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)
universe u v

theorem functionSystem.con_sing (p : FunToken A B) : FunCon A B {p} := by
  intro s hs _hin
  have hsub : funOutputUnion A B s ⊆ p.val.2 := by
    intro y hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
    have hq' : q = p := Finset.mem_singleton.mp (hs hq)
    cases hq'
    exact hy'
  exact B.con_subset p.property.2 hsub

theorem functionSystem.con_subset {w w' : Finset (FunToken A B)}
    (hw : FunCon A B w) (hw' : w' ⊆ w) : FunCon A B w' :=
  fun s hs hin => hw s (fun _ hq => hw' (hs hq)) hin

theorem functionSystem.ent_bot {w : Finset (FunToken A B)} (hw : FunCon A B w) :
    FunEnt A B w (funBot A B) :=
  ⟨hw, ∅, Finset.empty_subset _,
    fun q hq => False.elim (Finset.notMem_empty q hq),
    fun y hy => False.elim (Finset.notMem_empty y hy)⟩

theorem functionSystem.ent_con {w : Finset (FunToken A B)} {p : FunToken A B}
    (hEnt : FunEnt A B w p) : FunCon A B (insert p w) := by
  obtain ⟨hw, s, hs, hEntIn, hEntOut⟩ := hEnt
  intro t ht hin
  if hp : p ∈ t then
    let t' := t.filter (· ≠ p)
    have ht_eq : insert p t' = t := insert_filter_ne A B hp
    have ht'sub : t' ⊆ w := filter_ne_subset_of_subset_insert A B ht
    have hin' : p.val.1 ∪' funInputUnion A B t' ∈ A.Con := by
      rwa [← ht_eq, funInputUnion.insert] at hin
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
      rwa [funInputUnion.funion]
    have hout_union : funOutputUnion A B s ∪' funOutputUnion A B t' ∈ B.Con := by
      have : funOutputUnion A B (s ∪' t') ∈ B.Con := hw _ hsub hin_union
      rwa [funOutputUnion.funion] at this
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
      rwa [← ht_eq, funOutputUnion.insert]
    exact this
  else
    have ht' : t ⊆ w := by
      intro q hq
      have : q ∈ insert p w := ht hq
      rcases Finset.mem_insert.mp this with rfl | hqW
      · exact False.elim (hp hq)
      · exact hqW
    exact hw t ht' hin

theorem functionSystem.ent_refl {w : Finset (FunToken A B)} {p : FunToken A B}
    (hw : FunCon A B w) (hp : p ∈ w) : FunEnt A B w p :=
  ⟨hw, {p},
    fun q hq => by
      cases Finset.mem_singleton.mp hq
      exact hp,
    fun q hq => by
      cases Finset.mem_singleton.mp hq
      exact proposition_2_3_iii A p.property.1,
    by
      rw [funOutputUnion.singleton]
      exact proposition_2_3_iii B p.property.2⟩

theorem functionSystem.ent_trans {u v : Finset (FunToken A B)} {c : FunToken A B}
    (hv : FunCon A B v) (hu : FunCon A B u)
    (hEnts : ∀ y ∈ u, FunEnt A B v y) (hEnt : FunEnt A B u c) :
    FunEnt A B v c := by
  obtain ⟨_, s, hs, hEntIn, hEntOut⟩ := hEnt
  refine ⟨hv, ?_⟩
  have hWit : ∀ q ∈ s, ∃ s_q ⊆ v, (∀ r ∈ s_q, A.EntSet q.val.1 r.val.1) ∧
      B.EntSet (funOutputUnion A B s_q) q.val.2 := by
    intro q hq
    exact (hEnts q (hs hq)).2
  obtain ⟨S, hSsub, hSin, hSout⟩ :=
    exists_combined_witness A B hv c.property.1 hEntIn hWit
  refine ⟨S, hSsub, hSin, ?_⟩
  have hin_s : funInputUnion A B s ∈ A.Con :=
    funInputUnion.con_of_ent A B c.property.1 hEntIn
  have hout_s : funOutputUnion A B s ∈ B.Con := hu s hs hin_s
  have hin_S : funInputUnion A B S ∈ A.Con :=
    funInputUnion.con_of_ent A B c.property.1 hSin
  have hout_S : funOutputUnion A B S ∈ B.Con := hv S hSsub hin_S
  exact proposition_2_3_iv B hout_S hout_s hSout hEntOut

def functionSystem : InfoSys (FunToken A B) where
  bot := funBot A B
  Con := {w | FunCon A B w}
  Ent := FunEnt A B
  con_subset := functionSystem.con_subset A B
  con_sing := functionSystem.con_sing A B
  ent_con := functionSystem.ent_con A B
  ent_bot := functionSystem.ent_bot A B
  ent_refl := functionSystem.ent_refl A B
  ent_trans := functionSystem.ent_trans A B

end InfoSys

end DomainTheory.InformationSystems
