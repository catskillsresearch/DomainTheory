module

public import DomainTheory.InformationSystems.InformationSystems.PartialFunToken
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

def PartialFunConsistent {A B : Type*} (u : Finset (PartialFunToken A B)) : Prop :=
  ∀ ⦃a : A⦄ ⦃b b' : B⦄,
    PartialFunToken.pair a b ∈ u → PartialFunToken.pair a b' ∈ u → b = b'

def PartialFunEnt {A B : Type*} (u : Finset (PartialFunToken A B)) (X : PartialFunToken A B) : Prop :=
  PartialFunConsistent u ∧ (X = PartialFunToken.bot ∨ X ∈ u)

theorem consistent_empty {A B : Type*} :
    PartialFunConsistent (∅ : Finset (PartialFunToken A B)) := by
  intro _a _b _b' hb _
  exact False.elim (Finset.notMem_empty _ hb)

theorem consistent_subset {A B : Type*} {u v : Finset (PartialFunToken A B)} (huv : v ⊆ u)
    (hu : PartialFunConsistent u) : PartialFunConsistent v :=
  fun _a _b _b' hb hb' => hu (huv hb) (huv hb')

theorem consistent_singleton {A B : Type*} [DecidableEq A] [DecidableEq B]
    (t : PartialFunToken A B) : PartialFunConsistent ({t} : Finset (PartialFunToken A B)) := by
  intro a b b' hb hb'
  rw [Finset.mem_singleton] at hb hb'
  cases t with
  | bot =>
    cases hb
  | pair a0 b0 =>
    cases hb
    cases hb'
    rfl

theorem consistent_insert_bot {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (PartialFunToken A B)} (hu : PartialFunConsistent u) :
    PartialFunConsistent (insert (PartialFunToken.bot : PartialFunToken A B) u) := by
  intro a b b' hb hb'
  have hb1 : PartialFunToken.pair a b ∈ u := by
    rcases Finset.mem_insert.mp hb with h | h
    · cases h
    · exact h
  have hb2 : PartialFunToken.pair a b' ∈ u := by
    rcases Finset.mem_insert.mp hb' with h | h
    · cases h
    · exact h
  exact hu hb1 hb2

theorem consistent_insert_mem {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (PartialFunToken A B)} {t : PartialFunToken A B}
    (ht : t ∈ u) (hu : PartialFunConsistent u) : PartialFunConsistent (insert t u) := by
  simpa [Finset.insert_eq_of_mem ht] using hu

def partialFunctionSystem (A B : Type*) [DecidableEq A] [DecidableEq B] :
    InfoSys (PartialFunToken A B) where
  bot := PartialFunToken.bot
  Con := {u | PartialFunConsistent u}
  Ent := PartialFunEnt
  con_subset := by
    intro u v hu hv
    exact consistent_subset hv hu
  con_sing := fun t => consistent_singleton t
  ent_con := by
    rintro u a ⟨hu, hX⟩
    rcases hX with rfl | hmem
    · exact consistent_insert_bot hu
    · exact consistent_insert_mem hmem hu
  ent_bot := by
    intro u hu
    exact ⟨hu, Or.inl rfl⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, Or.inr ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, hc⟩
    refine ⟨hv, ?_⟩
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · have ⟨_, hcv⟩ := hvu c hc
      exact hcv

end DomainTheory.InformationSystems
