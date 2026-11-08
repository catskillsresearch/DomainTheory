module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Token

@[expose] public section

namespace DomainTheory.InformationSystems

def Sat (x : ℚ) : Token → Prop
  | .bot => True
  | .interval lo hi _ => (lo : ℚ) < x ∧ x < (hi : ℚ)

theorem sat_midpoint {lo hi : ℕ} (hlt : lo < hi) :
    Sat (((lo : ℚ) + (hi : ℚ)) / 2) (.interval lo hi hlt) := by
  have h2 : (0 : ℚ) < 2 := by norm_num
  have _hlo : (lo : ℚ) < (hi : ℚ) := Nat.cast_lt.mpr hlt
  constructor
  ·
    rw [lt_div_iff₀ h2]
    linarith
  · rw [div_lt_iff₀ h2]
    linarith

theorem sat_sing (t : Token) : ∃ x : ℚ, Sat x t := by
  cases t with
  | bot => exact ⟨0, trivial⟩
  | interval lo hi hlt => exact ⟨_, sat_midpoint hlt⟩

def ofSatisfaction {τ : Type*} [DecidableEq τ] {Point : Type*}
    (Sat : Point → τ → Prop) (bot : τ)
    (sat_bot : ∀ p, Sat p bot)
    (sat_sing : ∀ t, ∃ p, Sat p t) : InfoSys τ where
  bot := bot
  Con := {u | ∃ p, ∀ t ∈ u, Sat p t}
  Ent u X := (∃ p, ∀ t ∈ u, Sat p t) ∧ ∀ p, (∀ t ∈ u, Sat p t) → Sat p X
  con_subset := by
    rintro u v ⟨p, hp⟩ hsub
    exact ⟨p, fun t ht => hp t (hsub ht)⟩
  con_sing := by
    intro a
    obtain ⟨p, hp⟩ := sat_sing a
    exact ⟨p, fun t ht => by
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hp⟩
  ent_con := by
    rintro u a ⟨⟨p, hp⟩, hEnt⟩
    exact ⟨p, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact hEnt p hp
      · exact hp t ht'⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, fun p _ => sat_bot p⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, fun p hp => hp a ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, huEnt⟩
    refine ⟨hv, fun p hp => huEnt p ?_⟩
    intro y hy
    exact (hvu y hy).2 p hp

end DomainTheory.InformationSystems
