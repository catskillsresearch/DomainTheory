module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion
public import DomainTheory.InformationSystems.InformationSystems.EntSet
public import Mathlib.Data.Finset.Filter
import DomainTheory.InformationSystems.InformationSystems.InfoSys.con_empty

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

def FunToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : Finset α × Finset β // p.1 ∈ A.Con ∧ p.2 ∈ B.Con}

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

instance (A : InfoSys α) (B : InfoSys β) : DecidableEq (FunToken A B) :=
  fun p q =>
    match decidableEq_finset p.val.1 q.val.1, decidableEq_finset p.val.2 q.val.2 with
    | isTrue h1, isTrue h2 => isTrue (Subtype.ext (Prod.ext h1 h2))
    | isFalse n1, _ =>
        isFalse fun h => n1 (congrArg (fun r : FunToken A B => r.val.1) h)
    | isTrue _, isFalse n2 =>
        isFalse fun h => n2 (congrArg (fun r : FunToken A B => r.val.2) h)

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)
universe u v

theorem funBot.property : (∅ : Finset α) ∈ A.Con ∧ (∅ : Finset β) ∈ B.Con :=
  ⟨A.con_empty, B.con_empty⟩

def funBot : FunToken A B :=
  ⟨(∅, ∅), funBot.property A B⟩

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance instLeftCommutativeFunInput :
    LeftCommutative fun p : FunToken A B => (funion p.val.1 : Finset α → Finset α) :=
  ⟨fun p q s => funion.left_comm p.val.1 q.val.1 s⟩

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance instLeftCommutativeFunOutput :
    LeftCommutative fun p : FunToken A B => (funion p.val.2 : Finset β → Finset β) :=
  ⟨fun p q s => funion.left_comm p.val.2 q.val.2 s⟩

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_funInput (t : Multiset (FunToken A B)) (x : α) :
    x ∈ Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) t ↔
      ∃ p ∈ t, x ∈ p.val.1 := by
  refine Multiset.induction_on t ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, funion.mem, ih, Multiset.mem_cons]
    constructor
    · rintro (hx | ⟨q, hq, hx⟩)
      · exact ⟨p, Or.inl rfl, hx⟩
      · exact ⟨q, Or.inr hq, hx⟩
    · rintro ⟨q, hq, hx⟩
      rcases hq with rfl | hq
      · exact Or.inl hx
      · exact Or.inr ⟨q, hq, hx⟩

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_funOutput (t : Multiset (FunToken A B)) (y : β) :
    y ∈ Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) t ↔
      ∃ p ∈ t, y ∈ p.val.2 := by
  refine Multiset.induction_on t ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, funion.mem, ih, Multiset.mem_cons]
    constructor
    · rintro (hy | ⟨q, hq, hy⟩)
      · exact ⟨p, Or.inl rfl, hy⟩
      · exact ⟨q, Or.inr hq, hy⟩
    · rintro ⟨q, hq, hy⟩
      rcases hq with rfl | hq
      · exact Or.inl hy
      · exact Or.inr ⟨q, hq, hy⟩

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)
universe u v

def funInputUnion (s : Finset (FunToken A B)) : Finset α :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) s.1

theorem funInputUnion.empty : funInputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

theorem mem_funInputUnion {s : Finset (FunToken A B)} {x : α} :
    x ∈ funInputUnion A B s ↔ ∃ p ∈ s, x ∈ p.val.1 := by
  simpa [funInputUnion] using mem_foldr_funInput A B s.1 x

theorem entSet_inputUnion_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    A.EntSet u' (funInputUnion A B s) := by
  intro x hx
  rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
  exact h q hq x hx'

theorem funInputUnion.con_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (hu' : u' ∈ A.Con) (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    funInputUnion A B s ∈ A.Con :=
  A.con_subset (EntSet.union_mem A hu' (entSet_inputUnion_of_ent A B h))
    (funion.subset_right _ _)

theorem funInputUnion.funion (s t : Finset (FunToken A B)) :
    funInputUnion A B (s ∪' t) = funInputUnion A B s ∪' funInputUnion A B t := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
    rcases funion.mem.mp hp with hp | hp
    · exact funion.mem.mpr (Or.inl ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
    · exact funion.mem.mpr (Or.inr ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases funion.mem.mp hx with hx | hx
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, funion.mem.mpr (Or.inl hp), hx'⟩
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, funion.mem.mpr (Or.inr hp), hx'⟩

theorem funInputUnion.singleton (p : FunToken A B) :
    funInputUnion A B {p} = p.val.1 := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hx'
  · intro hx
    exact (mem_funInputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hx⟩

theorem funInputUnion.insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funInputUnion A B (Insert.insert p s) = p.val.1 ∪' funInputUnion A B s := by
  have h : Insert.insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact funion.mem.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact funion.mem.mpr (Or.inr hq)
    · intro hq
      rcases funion.mem.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funInputUnion.funion, funInputUnion.singleton]

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)
universe u v

def funOutputUnion (s : Finset (FunToken A B)) : Finset β :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) s.1

theorem funOutputUnion.empty : funOutputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

theorem mem_funOutputUnion {s : Finset (FunToken A B)} {y : β} :
    y ∈ funOutputUnion A B s ↔ ∃ p ∈ s, y ∈ p.val.2 := by
  simpa [funOutputUnion] using mem_foldr_funOutput A B s.1 y

theorem funOutputUnion.funion (s t : Finset (FunToken A B)) :
    funOutputUnion A B (s ∪' t) = funOutputUnion A B s ∪' funOutputUnion A B t := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
    rcases funion.mem.mp hp with hp | hp
    · exact funion.mem.mpr (Or.inl ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
    · exact funion.mem.mpr (Or.inr ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
  · intro hy
    rcases funion.mem.mp hy with hy | hy
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, funion.mem.mpr (Or.inl hp), hy'⟩
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, funion.mem.mpr (Or.inr hp), hy'⟩

theorem funOutputUnion.singleton (p : FunToken A B) :
    funOutputUnion A B {p} = p.val.2 := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hy'
  · intro hy
    exact (mem_funOutputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hy⟩

theorem funOutputUnion.insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funOutputUnion A B (Insert.insert p s) = p.val.2 ∪' funOutputUnion A B s := by
  have h : Insert.insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact funion.mem.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact funion.mem.mpr (Or.inr hq)
    · intro hq
      rcases funion.mem.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funOutputUnion.funion, funOutputUnion.singleton]

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def FunCon (w : Finset (FunToken A B)) : Prop :=
  ∀ s ⊆ w, funInputUnion A B s ∈ A.Con → funOutputUnion A B s ∈ B.Con

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem exists_combined_witness {u' : Finset α} {s : Finset (FunToken A B)}
    {v : Finset (FunToken A B)}
    (hv : FunCon A B v) (hu' : u' ∈ A.Con)
    (hEntIn : ∀ q ∈ s, A.EntSet u' q.val.1)
    (hWit : ∀ q ∈ s, ∃ s_q ⊆ v, (∀ r ∈ s_q, A.EntSet q.val.1 r.val.1) ∧
      B.EntSet (funOutputUnion A B s_q) q.val.2) :
    ∃ S ⊆ v, (∀ r ∈ S, A.EntSet u' r.val.1) ∧
      B.EntSet (funOutputUnion A B S) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · intro _ hq
      exact False.elim (Finset.notMem_empty _ hq)
    · intro y hy
      exact False.elim (Finset.notMem_empty y hy)
  | insert q s' hqnot ih =>
    have hEntIn' : ∀ r ∈ s', A.EntSet u' r.val.1 := fun r hr =>
      hEntIn r (Finset.mem_insert_of_mem hr)
    have hWit' : ∀ r ∈ s', ∃ s_r ⊆ v, (∀ t ∈ s_r, A.EntSet r.val.1 t.val.1) ∧
        B.EntSet (funOutputUnion A B s_r) r.val.2 := fun r hr =>
      hWit r (Finset.mem_insert_of_mem hr)
    obtain ⟨S', hS'sub, hS'in, hS'out⟩ := ih hEntIn' hWit'
    obtain ⟨Sq, hSqsub, hSqin, hSqout⟩ := hWit q (Finset.mem_insert_self q s')
    refine ⟨S' ∪' Sq, funion.subset_iff.mpr ⟨hS'sub, hSqsub⟩, ?_, ?_⟩
    · intro r hr
      rcases funion.mem.mp hr with hr | hr
      · exact hS'in r hr
      · have hEnt_q : A.EntSet u' q.val.1 := hEntIn q (Finset.mem_insert_self q s')
        have hEnt_r : A.EntSet q.val.1 r.val.1 := hSqin r hr
        exact EntSet.trans A hu' q.property.1 hEnt_q hEnt_r
    · rw [funOutputUnion.funion, funOutputUnion.insert]
      have hinS' : funInputUnion A B S' ∈ A.Con :=
        funInputUnion.con_of_ent A B hu' hS'in
      have houtS' : funOutputUnion A B S' ∈ B.Con := hv S' hS'sub hinS'
      have hinSq : funInputUnion A B Sq ∈ A.Con :=
        funInputUnion.con_of_ent A B q.property.1 hSqin
      have houtSq : funOutputUnion A B Sq ∈ B.Con := hv Sq hSqsub hinSq
      have hinUnion : funInputUnion A B (S' ∪' Sq) ∈ A.Con := by
        rw [funInputUnion.funion]
        have hEnt : A.EntSet u' (funInputUnion A B S' ∪' funInputUnion A B Sq) :=
          EntSet.union A
            (entSet_inputUnion_of_ent A B hS'in)
            (EntSet.trans A hu' q.property.1
              (hEntIn q (Finset.mem_insert_self q s'))
              (entSet_inputUnion_of_ent A B hSqin))
        exact A.con_subset (EntSet.union_mem A hu' hEnt) (funion.subset_right _ _)
      have houtUnion : funOutputUnion A B S' ∪' funOutputUnion A B Sq ∈ B.Con := by
        have : funOutputUnion A B (S' ∪' Sq) ∈ B.Con := hv _ (funion.subset_iff.mpr ⟨hS'sub, hSqsub⟩) hinUnion
        rwa [funOutputUnion.funion] at this
      have hEnt1 : B.EntSet (funOutputUnion A B S' ∪' funOutputUnion A B Sq)
          (funOutputUnion A B s') :=
        EntSet.mono B houtS' houtUnion (funion.subset_left _ _) hS'out
          (Finset.Subset.refl _)
      have hEnt2 : B.EntSet (funOutputUnion A B S' ∪' funOutputUnion A B Sq) q.val.2 :=
        EntSet.mono B houtSq houtUnion (funion.subset_right _ _) hSqout
          (Finset.Subset.refl _)
      exact EntSet.union B hEnt2 hEnt1

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def FunEnt (w : Finset (FunToken A B)) (p : FunToken A B) : Prop :=
  FunCon A B w ∧
    ∃ s ⊆ w, (∀ q ∈ s, A.EntSet p.val.1 q.val.1) ∧
      B.EntSet (funOutputUnion A B s) p.val.2

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem filter_ne_subset_of_subset_insert {p : FunToken A B}
    {t w : Finset (FunToken A B)} (ht : t ⊆ insert p w) :
    t.filter (· ≠ p) ⊆ w := by
  intro q hq
  have ⟨hqt, hne⟩ := Finset.mem_filter.mp hq
  have : q ∈ insert p w := ht hqt
  rcases Finset.mem_insert.mp this with rfl | hqW
  · exact False.elim (hne rfl)
  · exact hqW

end InfoSys

end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem insert_filter_ne {p : FunToken A B} {t : Finset (FunToken A B)}
    (hp : p ∈ t) : insert p (t.filter (· ≠ p)) = t := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (Finset.mem_filter.mp hq).1
  · intro hq
    if h : q = p then
      exact Finset.mem_insert.mpr (Or.inl h)
    else
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hq, h⟩))

end InfoSys

end DomainTheory.InformationSystems


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
    have hsub : s ∪' t' ⊆ w := funion.subset_iff.mpr ⟨hs, ht'sub⟩
    have hEnt_in_s : A.EntSet p.val.1 (funInputUnion A B s) :=
      entSet_inputUnion_of_ent A B hEntIn
    have hEnt_big : A.EntSet (p.val.1 ∪' funInputUnion A B t') (funInputUnion A B s) :=
      EntSet.mono A p.property.1 hin' (funion.subset_left _ _) hEnt_in_s
        (Finset.Subset.refl _)
    have hbig : (p.val.1 ∪' funInputUnion A B t') ∪' funInputUnion A B s ∈ A.Con :=
      EntSet.union_mem A hin' hEnt_big
    have hin_st' : funInputUnion A B s ∪' funInputUnion A B t' ∈ A.Con := by
      have heq :
          (p.val.1 ∪' funInputUnion A B t') ∪' funInputUnion A B s =
            p.val.1 ∪' (funInputUnion A B s ∪' funInputUnion A B t') := by
        rw [funion.assoc, funion.comm (funInputUnion A B t')]
      have hbig' : p.val.1 ∪' (funInputUnion A B s ∪' funInputUnion A B t') ∈ A.Con := by
        rwa [heq] at hbig
      exact A.con_subset hbig' (funion.subset_right _ _)
    have hin_union : funInputUnion A B (s ∪' t') ∈ A.Con := by
      rwa [funInputUnion.funion]
    have hout_union : funOutputUnion A B s ∪' funOutputUnion A B t' ∈ B.Con := by
      have : funOutputUnion A B (s ∪' t') ∈ B.Con := hw _ hsub hin_union
      rwa [funOutputUnion.funion] at this
    have hout_s : funOutputUnion A B s ∈ B.Con :=
      B.con_subset hout_union (funion.subset_left _ _)
    have hEnt_out' : B.EntSet (funOutputUnion A B s ∪' funOutputUnion A B t') p.val.2 :=
      EntSet.mono B hout_s hout_union (funion.subset_left _ _) hEntOut
        (Finset.Subset.refl _)
    have hfinal :
        (funOutputUnion A B s ∪' funOutputUnion A B t') ∪' p.val.2 ∈ B.Con :=
      EntSet.union_mem B hout_union hEnt_out'
    have hout_t : p.val.2 ∪' funOutputUnion A B t' ∈ B.Con := by
      have heq :
          (funOutputUnion A B s ∪' funOutputUnion A B t') ∪' p.val.2 =
            funOutputUnion A B s ∪' (p.val.2 ∪' funOutputUnion A B t') := by
        rw [funion.assoc, funion.comm (funOutputUnion A B t')]
      have hfinal' :
          funOutputUnion A B s ∪' (p.val.2 ∪' funOutputUnion A B t') ∈ B.Con := by
        rwa [heq] at hfinal
      exact B.con_subset hfinal' (funion.subset_right _ _)
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
      exact EntSet.refl A p.property.1,
    by
      rw [funOutputUnion.singleton]
      exact EntSet.refl B p.property.2⟩

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
  exact EntSet.trans B hout_S hout_s hSout hEntOut

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
