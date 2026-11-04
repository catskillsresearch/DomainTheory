module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem
import DomainTheory.DataTypesAsLattices.Retracts.retract_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

namespace RestrictedEquiv

def mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

def Ea (a : Pomega) : RestrictedEquiv where
  rel := fun x y => typed x a ∧ typed y a ∧ x = y
  symm := by
    intro x y ⟨hx, hy, h⟩
    exact ⟨hy, hx, h.symm⟩
  trans := by
    intro x y z ⟨hx, hy, hxy⟩ ⟨_, hz, hyz⟩
    exact ⟨hx, hz, hxy.trans hyz⟩

def arrowE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun f g =>
    f = graph (fun x => funOf f x) ∧
      g = graph (fun x => funOf g x) ∧
        ∀ x y, A.rel x y → B.rel (funOf f x) (funOf g y)
  symm := by
    intro f g ⟨hf, hg, h⟩
    exact ⟨hg, hf, fun x y hxy => B.symm (h y x (A.symm hxy))⟩
  trans := by
    intro f g k ⟨hf, hg, hfg⟩ ⟨hg', hk, hgk⟩
    exact ⟨hf, hk, fun x y hxy =>
      B.trans (hfg x y hxy) (hgk y y (A.trans (A.symm hxy) hxy))⟩

def prodE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
      v = pairElem (funOf v (ofNat 0)) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 0)) (funOf v (ofNat 0)) ∧
          B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))
  symm := by
    intro u v ⟨hu, hv, h0, h1⟩
    exact ⟨hv, hu, A.symm h0, B.symm h1⟩
  trans := by
    intro u v w ⟨hu, hv, h0, h1⟩ ⟨hv', hw, k0, k1⟩
    exact ⟨hu, hw, A.trans h0 k0, B.trans h1 k1⟩

def sumE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 0) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))) ∨
      (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 1) (funOf v (ofNat 1)) ∧
        B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1)))
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · exact Or.inl ⟨hv, hu, A.symm hA⟩
    · exact Or.inr ⟨hv, hu, B.symm hB⟩
  trans := by
    intro u v w h1 h2
    rcases h1 with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · rcases h2 with ⟨hv', hw, hA'⟩ | ⟨hv', hw, _⟩
      · exact Or.inl ⟨hu, hw, A.trans hA hA'⟩
      · exact (pairElem.tag_ne (funOf v (ofNat 1)) (funOf v (ofNat 1))
          (hv.symm.trans hv')).elim
    · rcases h2 with ⟨hv', hw, _⟩ | ⟨hv', hw, hB'⟩
      · exact (pairElem.tag_ne (funOf v (ofNat 1)) (funOf v (ofNat 1))
          (hv'.symm.trans hv)).elim
      · exact Or.inr ⟨hu, hw, B.trans hB hB'⟩

def emptyE : RestrictedEquiv where
  rel := fun _ _ => False
  symm := fun h => False.elim h
  trans := fun h _ => False.elim h

def singletonE (a : Pomega) : RestrictedEquiv where
  rel := fun x y => x = a ∧ y = a
  symm := by
    intro x y ⟨hx, hy⟩
    exact ⟨hy, hx⟩
  trans := by
    intro x y z ⟨hx, _hy⟩ ⟨_hy', hz⟩
    exact ⟨hx, hz⟩

def Nk (k : ℕ) : RestrictedEquiv where
  rel := fun x y => (∃ n < k, x = ofNat n) ∧ x = y
  symm := by
    intro x y ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro x y z ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

def Nrel : RestrictedEquiv where
  rel := fun x y => (∃ n, x = ofNat n) ∧ x = y
  symm := by
    intro x y ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro x y z ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

def kerE (a : Pomega) : RestrictedEquiv where
  rel := fun x y => funOf a x = funOf a y
  symm := by
    intro x y h
    exact h.symm
  trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz

end RestrictedEquiv

export RestrictedEquiv (Ea arrowE prodE sumE emptyE singletonE Nk Nrel kerE)

namespace singletonE

theorem mem (a x : Pomega) : (singletonE a).mem x ↔ x = a :=
  ⟨fun h => h.1, fun hx => ⟨hx, hx⟩⟩

end singletonE

namespace kerE

theorem repr {a : Pomega} (ha : Retract a) (x : Pomega) :
    (kerE a).rel x (funOf a x) :=
  (retract_app ha x).symm

end kerE

end DomainTheory.DataTypesAsLattices
