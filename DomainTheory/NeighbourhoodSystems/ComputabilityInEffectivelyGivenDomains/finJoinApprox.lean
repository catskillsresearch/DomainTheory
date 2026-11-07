module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive
namespace NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α)

theorem PDsingleton_mono {X X' : Set α} (hX : V.mem X) (hX' : V.mem X') (hX'X : X' ⊆ X) :
    V.PDsingleton (V.principal hX) ≤ V.PDsingleton (V.principal hX') := by
  intro W hW
  rw [PDmem_singleton] at hW ⊢
  obtain ⟨Y, hYpr, hPD, hsub⟩ := hW
  rw [mem_principal] at hYpr
  exact ⟨Y, ⟨hYpr.1, hX'X.trans hYpr.2⟩, hPD, hsub⟩

def PDsingletonApproxMap : ApproximableMap V V.PowerDomain :=
  ofMono (fun _X hX => V.PDsingleton (V.principal hX))
    (fun X X' hX hX' hX'X => @PDsingleton_mono α V X X' hX hX' hX'X)

@[simp] theorem PDsingletonApproxMap_rel {X : Set α} {W : Set (Set α)} (hX : V.mem X) :
    (PDsingletonApproxMap (V := V)).rel X W ↔ (V.PDsingleton (V.principal hX)).mem W := by
  dsimp [PDsingletonApproxMap, ofMono]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨hX, h⟩

def PDsingletonMeet (a b : V.PowerDomain.Element) : V.PowerDomain.Element where
  mem W := a.mem W ∧ b.mem W
  sub h := a.sub h.1
  master_mem := ⟨a.master_mem, b.master_mem⟩
  inter_mem h1 h2 := ⟨a.inter_mem h1.1 h2.1, b.inter_mem h1.2 h2.2⟩
  up_mem h hW hsub := ⟨a.up_mem h.1 hW hsub, b.up_mem h.2 hW hsub⟩

@[simp] theorem PDsingletonMeet_mem {a b : V.PowerDomain.Element} {W : Set (Set α)} :
    (V.PDsingletonMeet a b).mem W ↔ a.mem W ∧ b.mem W := Iff.rfl

def PDfinJoinApproxMap₂ : ApproximableMap₂ V V V.PowerDomain where
  rel X Y W := (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W
  rel_dom₀ h := (PDsingletonApproxMap (V := V)).rel_dom h.1
  rel_dom₁ h := (PDsingletonApproxMap (V := V)).rel_dom h.2
  rel_cod h := (PDsingletonApproxMap (V := V)).rel_cod h.1
  master_rel := ⟨(PDsingletonApproxMap (V := V)).master_rel, (PDsingletonApproxMap (V := V)).master_rel⟩
  inter_right := fun ⟨h1, h2⟩ ⟨h1', h2'⟩ =>
    ⟨(PDsingletonApproxMap (V := V)).inter_right h1 h1',
      (PDsingletonApproxMap (V := V)).inter_right h2 h2'⟩
  mono := fun ⟨h1, h2⟩ hXX' hYY' hWW' hX' hY' hW' =>
    ⟨(PDsingletonApproxMap (V := V)).mono h1 hXX' hWW' hX' hW',
      (PDsingletonApproxMap (V := V)).mono h2 hYY' hWW' hY' hW'⟩

def finJoinMap_prod : ApproximableMap (prod V V) V.PowerDomain := ofMap₂ (PDfinJoinApproxMap₂ (V := V))

@[simp] theorem finJoinMap_prod_rel {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (finJoinMap_prod (V := V)).rel (prodNbhd X Y) W ↔
      (PDfinJoinApproxMap₂ (V := V)).rel X Y W := by
  dsimp [finJoinMap_prod, ofMap₂]
  simp only [prodNbhd.inl_preimage, prodNbhd.inr_preimage]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨prod_mem_prodNbhd hX hY, h⟩⟩

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

theorem PDext {a b : V.PowerDomain.Element} (h : ∀ W, a.mem W ↔ b.mem W) : a = b :=
  @Element.ext (Set α) V.PowerDomain a b h

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem PDfinJoinApproxMap₂_rel_iff {X Y : Set α} (_hX : V.mem X) (_hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W := Iff.rfl

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

theorem PDfinJoin_pair (x y : V.Element) :
    V.PDfinJoin 2 ![x, y] = V.PDsingletonMeet (V.PDsingleton x) (V.PDsingleton y) := by
  apply PDext
  intro W
  simp only [PDsingletonMeet_mem, PDmem_singleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨⟨X 0, hX 0, hPD, hsub 0⟩, ⟨X 1, hX 1, hPD, hsub 1⟩⟩
  · rintro ⟨⟨X0, hx, hPD, hsub0⟩, ⟨X1, hy, _, hsub1⟩⟩
    refine ⟨![X0, X1], ?_, hPD, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

theorem PDfinJoin_inter_two (x y : V.Element) {W : Set (Set α)} :
    (V.PDfinJoin 2 ![x, y]).mem W ↔
      (V.PDsingleton x).mem W ∧ (V.PDsingleton y).mem W := by
  rw [← PDsingletonMeet_mem, ← PDfinJoin_pair]

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem PDfinJoinApproxMap₂_rel_PD {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (V.PDfinJoin 2 ![V.principal hX, V.principal hY]).mem W := by
  constructor
  · intro ⟨h1, h2⟩
    rw [PDsingletonApproxMap_rel (hX := hX)] at h1
    rw [PDsingletonApproxMap_rel (hX := hY)] at h2
    exact (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).2 ⟨h1, h2⟩
  · intro h
    rcases (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).1 h with ⟨h1, h2⟩
    exact ⟨by rw [PDsingletonApproxMap_rel (hX := hX)]; exact h1,
      by rw [PDsingletonApproxMap_rel (hX := hY)]; exact h2⟩

theorem PDsingletonApproxMap_rel_Ypd_iff {n k : ℕ} :
    ((PDsingletonApproxMap (V := V))).rel (P.X n) (V.Ypd P k) ↔
      ∃ b ∈ decodeList k, P.X n ⊆ P.X b := by
  rw [PDsingletonApproxMap_rel (hX := P.mem_X n), PDmem_singleton, PowerDomain_mem]
  constructor
  · rintro ⟨Y, hYpr, _, hsub⟩
    have hn : P.X n ∈ V.upSet Y := ⟨P.mem_X n, hYpr.2⟩
    obtain ⟨b, hb, hPab⟩ := (V.mem_Ypd P).mp (hsub hn)
    exact ⟨b, hb, hPab.2⟩
  · intro ⟨b, hb, hnb⟩
    refine ⟨P.X b, ⟨P.mem_X b, hnb⟩, V.Ypd_isPDmem P k,
      (V.upSet_subset_Ypd_iff P).mpr ⟨b, hb, subset_rfl⟩⟩

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

theorem PDsingletonApproxMap_toElementMap (x : V.Element) :
    (PDsingletonApproxMap (V := V)).toElementMap x = V.PDsingleton x := by
  apply PDext
  intro W
  rw [ApproximableMap.mem_toElementMap, PDmem_singleton]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    rw [PDsingletonApproxMap_rel (hX := x.sub hxX)] at hrel
    rw [PDmem_singleton] at hrel
    obtain ⟨Y, ⟨hYmem, hXY⟩, hPD, hsub⟩ := hrel
    exact ⟨Y, x.up_mem hxX hYmem hXY, hPD, hsub⟩
  · intro hW
    obtain ⟨Y, hy, hPD, hsub⟩ := hW
    refine ⟨Y, hy, ?_⟩
    rw [PDsingletonApproxMap_rel (hX := x.sub hy), PDmem_singleton]
    exact ⟨Y, ⟨x.sub hy, subset_rfl⟩, hPD, hsub⟩

theorem PDfinJoinApproxMap₂_toElementMap (x y : V.Element) :
    (PDfinJoinApproxMap₂ (V := V)).toElementMap₂ x y = V.PDfinJoin 2 ![x, y] := by
  apply PDext
  intro W
  rw [PDfinJoin_inter_two, ApproximableMap₂.mem_toElementMap₂]
  constructor
  · rintro ⟨X, Y, hxX, hyY, ⟨h1, h2⟩⟩
    constructor
    · rw [← PDsingletonApproxMap_toElementMap (V := V)]
      exact (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) x).mpr ⟨X, hxX, h1⟩
    · rw [← PDsingletonApproxMap_toElementMap (V := V)]
      exact (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) y).mpr ⟨Y, hyY, h2⟩
  · intro ⟨h1, h2⟩
    rw [← PDsingletonApproxMap_toElementMap (V := V)] at h1 h2
    obtain ⟨X, hxX, hrelX⟩ :=
      (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) x).mp h1
    obtain ⟨Y, hyY, hrelY⟩ :=
      (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) y).mp h2
    exact ⟨X, Y, hxX, hyY, hrelX, hrelY⟩

theorem PDsingleton_principal {X : Set α} (hX : V.mem X) :
    V.PDsingleton (V.principal hX) =
      V.PowerDomain.principal (V.PDmem_upSet hX) := by
  apply PDext
  intro W
  rw [PDmem_singleton, mem_principal, PowerDomain_mem]
  constructor
  · rintro ⟨Y, ⟨hYmem, hXY⟩, hPD, hsub⟩
    exact ⟨hPD, ((V.upSet_subset_iff hX).mpr hXY).trans hsub⟩
  · rintro ⟨hPD, hsub⟩
    exact ⟨X, ⟨hX, subset_rfl⟩, hPD, hsub⟩

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

theorem ext_of_principal {β : Type*} {W : NeighborhoodSystem β}
    {f g : ApproximableMap V W}
    (h : ∀ (X : Set α) (hX : V.mem X),
      f.toElementMap (V.principal hX) = g.toElementMap (V.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

theorem finJoinMap_prod_toElementMap (x y : V.Element) :
    (finJoinMap_prod (V := V)).toElementMap (pair x y) = V.PDfinJoin 2 ![x, y] := by
  have hmap : toMap₂ (finJoinMap_prod (V := V)) = PDfinJoinApproxMap₂ (V := V) := toMap₂_ofMap₂ _
  rw [← toElementMap₂_toMap₂ (finJoinMap_prod (V := V)), hmap, PDfinJoinApproxMap₂_toElementMap]

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

theorem singleton_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ComputableMap P (V.PDPresentation P cons hconsp hcons) ((PDsingletonApproxMap (V := V))) := by
  constructor
  have h := P.incl_computable.swap.bExistsList.swap
  refine (RecDecidable.of_iff (fun s => ?_) h).re
  show PDsingletonApproxMap (V := V).rel (P.X s.unpair.1) ((V.PDPresentation P cons hconsp hcons).X s.unpair.2) ↔
      ∃ e ∈ decodeList s.unpair.2, P.X s.unpair.1 ⊆ P.X e
  simp only [PDPresentation]
  apply PDsingletonApproxMap_rel_Ypd_iff (V := V)

theorem PDfinJoinApproxMap₂_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ComputableMap (prodPresentation P P)
      (V.PDPresentation P cons hconsp hcons) (finJoinMap_prod (V := V)) := by
  constructor
  have hs : REPred (fun s => (PDsingletonApproxMap (V := V)).rel (P.X s.unpair.1) (V.Ypd P s.unpair.2)) :=
    (singleton_isComputable (V := V) P cons hconsp hcons).out
  have hra : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  have hrb : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine REPred.of_iff (fun t => by
    dsimp [prodPresentation_X, finJoinMap_prod, ofMap₂]
    simp only [prodNbhd.inl_preimage, prodNbhd.inr_preimage,
      PDPresentation, unpair_pair_fst, unpair_pair_snd]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩⟩
      exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩
      refine ⟨prod_mem_prodNbhd (P.mem_X _) (P.mem_X _), h1, h2⟩) ((hs.comp hra).and (hs.comp hrb))

end NeighborhoodSystem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

end


end DomainTheory.NeighbourhoodSystems
