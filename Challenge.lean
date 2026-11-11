module
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.RE
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Directed
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.Order
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Ideal
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Basic
@[expose] public section
namespace DomainTheory.NeighbourhoodSystems
structure NeighborhoodSystem (α : Type*) where
  mem : Set α → Prop
  master : Set α
  master_nonempty : master.Nonempty
  master_mem : mem master
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master
namespace NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α)
structure Element where
  mem : Set α → Prop
  sub : ∀ {X}, mem X → V.mem X
  master_mem : mem V.master
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y
def element_le (x y : V.Element) : Prop := ∀ X, x.mem X → y.mem X
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X := fun _ h => h
theorem element_le_trans (x y z : V.Element) (hxy : ∀ X, x.mem X → y.mem X)
    (hyz : ∀ X, y.mem X → z.mem X) : ∀ X, x.mem X → z.mem X := fun X h => hyz X (hxy X h)
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩; rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X); subst hmem; rfl
theorem element_le_antisymm (x y : V.Element) (hxy : ∀ X, x.mem X → y.mem X)
    (hyx : ∀ X, y.mem X → x.mem X) : x = y := @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩
instance : PartialOrder V.Element where
  le := element_le V; le_refl := element_le_refl V; le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.InformationSystems
universe u
structure InfoSys (α : Type u) [DecidableEq α] where
  bot : α
  Con : Set (Finset α)
  Ent : Finset α → α → Prop
  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con
  con_sing : ∀ a : α, {a} ∈ Con
  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con
  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot
  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a
  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c
namespace InfoSys
set_option linter.unusedSectionVars false
variable {α : Type u} [DecidableEq α] (sys : InfoSys α)
structure Element where
  carrier : Set α
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier
namespace Element
theorem ext {x y : sys.Element} (h : x.carrier = y.carrier) : x = y := by
  cases x; cases y; subst h; rfl
theorem le_refl (x : sys.Element) : x.carrier ⊆ x.carrier := Set.Subset.refl _
theorem le_trans (x y z : sys.Element) (hxy : x.carrier ⊆ y.carrier)
    (hyz : y.carrier ⊆ z.carrier) : x.carrier ⊆ z.carrier := Set.Subset.trans hxy hyz
theorem le_antisymm (x y : sys.Element) (hxy : x.carrier ⊆ y.carrier)
    (hyx : y.carrier ⊆ x.carrier) : x = y := ext sys (Set.Subset.antisymm hxy hyx)
instance instPartialOrder : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl := le_refl sys; le_trans := le_trans sys; le_antisymm := le_antisymm sys
end Element
noncomputable def closure {α : Type*} [DecidableEq α] (sys : InfoSys α)
    (u : Finset α) (hu : u ∈ sys.Con) : sys.Element :=
  let _ := u; let _ := hu; sorry
namespace treeSystem
inductive TreeToken (α : Type u) where
  | bot : TreeToken α
  | atom : α → TreeToken α
  | pairL : TreeToken α → TreeToken α
  | pairR : TreeToken α → TreeToken α
instance instDecidableEqTreeToken {α : Type u} [DecidableEq α] :
    DecidableEq (TreeToken α)
  | .bot, .bot => isTrue rfl
  | .atom a, .atom b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (TreeToken.atom.inj h')
  | .pairL a, .pairL b => match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl) | isFalse h => isFalse fun h' => h (TreeToken.pairL.inj h')
  | .pairR a, .pairR b => match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl) | isFalse h => isFalse fun h' => h (TreeToken.pairR.inj h')
  | .bot, .atom _ | .bot, .pairL _ | .bot, .pairR _ => isFalse fun h => nomatch h
  | .atom _, .bot | .atom _, .pairL _ | .atom _, .pairR _ => isFalse fun h => nomatch h
  | .pairL _, .bot | .pairL _, .atom _ | .pairL _, .pairR _ => isFalse fun h => nomatch h
  | .pairR _, .bot | .pairR _, .atom _ | .pairR _, .pairL _ => isFalse fun h => nomatch h
end treeSystem
open treeSystem
section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
inductive SumToken (α β : Type*) where
  | left : α → SumToken α β
  | right : β → SumToken α β
  | bot : SumToken α β
instance instDecidableEqSumToken : DecidableEq (SumToken α β)
  | .left a, .left b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.left.inj h')
  | .right a, .right b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.right.inj h')
  | .bot, .bot => isTrue rfl
  | .left _, .right _ | .left _, .bot | .right _, .left _ => isFalse fun h => nomatch h
  | .right _, .bot | .bot, .left _ | .bot, .right _ => isFalse fun h => nomatch h
class IsProdToken (A : InfoSys α) (B : InfoSys β) (p : α × β) : Prop where
  out : p.1 = A.bot ∨ p.2 = B.bot
instance (A : InfoSys α) (B : InfoSys β) (p : α × β) : Decidable (IsProdToken A B p) :=
  if h1 : p.1 = A.bot then isTrue ⟨Or.inl h1⟩
  else if h2 : p.2 = B.bot then isTrue ⟨Or.inr h2⟩
  else isFalse fun h => h.out.elim h1 h2
def ProdToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : α × β // IsProdToken A B p}
instance instDecidableEqProdToken (A : InfoSys α) (B : InfoSys β) :
    DecidableEq (ProdToken A B) := Subtype.instDecidableEq
end
section
variable {α : Type*} [DecidableEq α] (A : InfoSys α)
noncomputable def treeSystem : InfoSys (TreeToken α) :=
  let _ := A
  sorry
noncomputable def treeRhs :
    InfoSys (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  let _ := A
  sorry
end
end InfoSys
end DomainTheory.InformationSystems
namespace DomainTheory.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
def ScottOpen (U : Set D) : Prop :=
  open CompleteLattice in
  letI : LE D := (toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : SupSet D := (toCompleteSemilatticeSup (α := D)).toSupSet
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty
def WayBelow (x y : D) : Prop :=
  letI : LE D := (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
  letI : Preorder D := (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x
@[inherit_doc] scoped infix:50 " ≪ " => WayBelow
end DomainTheory.ContinuousLattice
namespace DomainTheory
open scoped DomainTheory.ContinuousLattice
universe u
class ContinuousLattice (D : Type u) [CompleteLattice D] : Prop where
  out : letI : LE D :=
    (CompleteLattice.toCompleteSemilatticeInf (α := D)).toPartialOrder.toPreorder.toLE
    ∀ y : D, IsLUB {x | x ≪ y} y
  sSup_wayBelow : ∀ y : D, sSup {x | x ≪ y} = y := fun y => (out y).sSup_eq
end DomainTheory
namespace DomainTheory.BridgeTheorems
open DomainTheory
open DomainTheory.NeighbourhoodSystems
open DomainTheory.InformationSystems
open DomainTheory.ContinuousLattice
open scoped DomainTheory.ContinuousLattice
structure NbhdBasis (ι α : Type*) [DecidableEq ι] where
  system : NeighborhoodSystem α
  nbhd : ι → Set α
  nbhd_mem : ∀ i, system.mem (nbhd i)
  exhaustive : ∀ {X : Set α}, system.mem X → ∃ i, nbhd i = X
  botIdx : ι
  botIdx_eq : nbhd botIdx = system.master
namespace NbhdBasis
variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)
include B
noncomputable def toInfoSys : InfoSys ι :=
  let _ := B
  sorry
noncomputable def domainOrderIso : B.system.Element ≃o B.toInfoSys.Element :=
  sorry
end NbhdBasis
noncomputable def neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι]
    (B : NbhdBasis ι α) : InfoSys ι :=
  let _ := B
  sorry
namespace InfoSysToNeighborhood
variable {α : Type*} [DecidableEq α] (A : InfoSys α)
include A
noncomputable def toNeighborhoodSystem : NeighborhoodSystem A.Element :=
  sorry
noncomputable def domainOrderIso : A.Element ≃o (toNeighborhoodSystem A).Element :=
  sorry
end InfoSysToNeighborhood
noncomputable abbrev infoSys_to_neighborhoodSystem {α : Type*} [DecidableEq α]
    (A : InfoSys α) : NeighborhoodSystem A.Element :=
  InfoSysToNeighborhood.toNeighborhoodSystem A
namespace ContinuousLatticeToNeighborhood
variable {D : Type*} [CompleteLattice D]
def wayBelowUp (a : D) : Set D := {z | a ≪ z}
noncomputable def toNeighborhoodSystem : NeighborhoodSystem D :=
  let _ := (⊥ : D)
  sorry
abbrev Filter : Type _ :=
  (toNeighborhoodSystem : NeighborhoodSystem D).Element
class Round (f : Filter (D := D)) : Prop where
  out : ∀ {a : D}, f.mem (wayBelowUp a) → ∃ b : D, a ≪ b ∧ f.mem (wayBelowUp b)
abbrev RoundFilter : Type _ :=
  { f : Filter (D := D) // Round f }
end ContinuousLatticeToNeighborhood
open ContinuousLatticeToNeighborhood
open DomainTheory.InformationSystems.InfoSys
open treeSystem
open Order
section Continuous
variable {D : Type*} [CompleteLattice D] [DecidableEq D]
noncomputable def wayBelowNbhdBasis : NbhdBasis D D where
  system := toNeighborhoodSystem; nbhd := wayBelowUp; nbhd_mem := fun _ => sorry
  exhaustive := fun {_} _ => sorry; botIdx := ⊥; botIdx_eq := sorry
class IsRoundInfoSysElement (e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element) : Prop where
  out : Round ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm e)
abbrev RoundInfoSysElement : Type _ :=
  { e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element // IsRoundInfoSysElement (D := D) e }
variable (hD : ContinuousLattice D)
include hD
noncomputable def presentation_domains_equiv :
    D ≃o RoundInfoSysElement (D := D) := by
  have := hD
  sorry
theorem exists_presentation_domains_equiv :
    Nonempty (D ≃o RoundInfoSysElement (D := D)) := by
  have := hD
  sorry
end Continuous
noncomputable def lowerBoundSystem : InfoSys ℕ := by
  sorry
noncomputable abbrev SexSys : InfoSys (TreeToken ℕ) :=
  treeSystem lowerBoundSystem
noncomputable abbrev SexRhs : InfoSys (SumToken ℕ (ProdToken SexSys SexSys)) :=
  treeRhs lowerBoundSystem
namespace InfoSysToIdealCompletion
variable {α : Type*} [DecidableEq α] (A : InfoSys α)
abbrev FiniteElement : Type _ :=
  { x : A.Element // ∃ (u : Finset α) (hu : u ∈ A.Con), x = A.closure u hu }
end InfoSysToIdealCompletion
noncomputable def sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element := by
  sorry
noncomputable def sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) := by
  sorry
noncomputable def sexDomainEquationIso :
    SexSys.Element ≃o SexRhs.Element := by
  sorry
theorem exists_sexNeighborhoodIso :
    Nonempty (SexSys.Element ≃o
      (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element) := by
  sorry
theorem exists_sexIdealIso :
    Nonempty (SexSys.Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement SexSys)) := by
  sorry
theorem exists_sexDomainEquationIso :
    Nonempty (SexSys.Element ≃o SexRhs.Element) := by
  sorry
end DomainTheory.BridgeTheorems
namespace DomainTheory.DataTypesAsLattices
open TopologicalSpace Topology Function
abbrev Pomega := Set ℕ
def e (n : ℕ) : Pomega := {k | n.testBit k}
def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m
def triangle (w : ℕ) : ℕ := w * (w + 1) / 2
theorem pair_eq_triangle (n m : ℕ) : pair n m = triangle (n + m) + m := rfl
theorem triangle_succ (w : ℕ) : triangle (w + 1) = triangle w + (w + 1) := by sorry
theorem triangle_le_of_le {a b : ℕ} (h : a ≤ b) : triangle a ≤ triangle b := by sorry
theorem triangle_lt_of_lt {a b : ℕ} (h : a < b) : triangle a < triangle b := by sorry
theorem triangle_le_pair (n m : ℕ) :
    triangle (n + m) ≤ pair n m ∧ pair n m < triangle (n + m + 1) := by sorry
theorem pair_inj {n₁ m₁ n₂ m₂ : ℕ} (h : pair n₁ m₁ = pair n₂ m₂) :
    n₁ = n₂ ∧ m₁ = m₂ := by sorry
theorem pair_le_left (n m : ℕ) : n ≤ pair n m := by sorry
theorem pair_le_right (n m : ℕ) : m ≤ pair n m :=
  Nat.le_add_left _ _
theorem exists_triangle_bucket (k : ℕ) :
    ∃ w, triangle w ≤ k ∧ k < triangle (w + 1) := by sorry
theorem exists_pair (k : ℕ) : ∃ n m, pair n m = k := by sorry
noncomputable def unpair (k : ℕ) : ℕ × ℕ :=
  ((exists_pair k).choose, (exists_pair k).choose_spec.choose)
theorem pair_unpair (k : ℕ) : pair (unpair k).1 (unpair k).2 = k :=
  (exists_pair k).choose_spec.choose_spec
theorem pair_lt_left (n m : ℕ) : n < pair n m + 1 :=
  Nat.lt_succ_of_le (pair_le_left n m)
theorem pair_lt_right (n m : ℕ) : m < pair n m + 1 :=
  Nat.lt_succ_of_le (pair_le_right n m)
def botElem : Pomega := ∅
def topElem : Pomega := Set.univ
def ofNat (n : ℕ) : Pomega := {n}
def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}
def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n
class IsScottContinuous (f : Pomega → Pomega) : Prop where
  out : ∀ x, f x = scottUnion f x
theorem mem_scottUnion {f : Pomega → Pomega} {x : Pomega} {k : ℕ} :
    k ∈ scottUnion f x ↔ ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by sorry
def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}
def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}
instance : TopologicalSpace Pomega :=
  .generateFrom (Set.range memOpen)
def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n
def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}
def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}
infixl:70 " ⬝ " => funOf
theorem funOf_isScottContinuous (u : Pomega) : IsScottContinuous (funOf u) := by sorry
class IsGraph (u : Pomega) : Prop where
  out : ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))
class Retract (a : Pomega) : Prop where
  out : a = comp a a
def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a
def typed (u a : Pomega) : Prop :=
  u = funOf a u
def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}
class DirectedSubset {f : Pomega → Pomega} (s : Set (Fixpoints f)) : Prop where
  out : s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, (x : Pomega) ⊆ z ∧ (y : Pomega) ⊆ z
def IsCompactSubset {f : Pomega → Pomega} (x : Fixpoints f) : Prop :=
  ∀ s : Set (Fixpoints f),
    DirectedSubset s →
      (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
      ∃ z ∈ s, (x : Pomega) ⊆ z
def IsStrict (a : Pomega) : Prop :=
  funOf a botElem = botElem
def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)
def RetractInverseLimit (F : Pomega → Pomega) :=
  {v : ℕ → Pomega //
    (∀ n, typed (v n) (iterateBot F n)) ∧
      ∀ n, v n = funOf (iterateBot F n) (v (n + 1))}
instance (F : Pomega → Pomega) : PartialOrder (RetractInverseLimit F) where
  le v w := ∀ n, v.1 n ⊆ w.1 n
  le_refl _ _ := subset_rfl
  le_trans _ _ _ hvw hwz n := subset_trans (hvw n) (hwz n)
  le_antisymm v w hvw hwv := by
    apply Subtype.ext
    funext n
    exact Set.Subset.antisymm (hvw n) (hwv n)
def iterateFrom (f : Pomega → Pomega) (x : Pomega) : ℕ → Pomega
  | 0 => x
  | n + 1 => f (iterateFrom f x n)
def lfpAbove (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, iterateFrom f x n
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}
def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n
def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))
def Icomb : Pomega := graph (fun x => x)
def Kcomb : Pomega := graph (fun x => graph (fun _ => x))
def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))
def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))
def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}
def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}
def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}
def dcondSet (z x y : Pomega) : Pomega :=
  condSet z (condSet z x topElem) (condSet z topElem y)
def seq2 (x y : Pomega) : Pomega :=
  graph (fun z => condSet z x (condSet (predSet z) y botElem))
def seqCons (x xs : Pomega) : Pomega :=
  graph (fun z => condSet z x (funOf xs (predSet z)))
def pairSeq (x y : Pomega) : Pomega := seq2 x y
def pairElem (x y : Pomega) : Pomega := seq2 x y
def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))
def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))
def applyNat (n m : ℕ) : ℕ := pair n m + 1
def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)
def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))
def extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (y : Y) : Pomega :=
  ⋃₀ { t | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ t = ⋂₀ (f '' {x : X | ↑x ∈ U}) }
def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term
def envSet (ρ : ℕ → Pomega) (i : ℕ) (v : Pomega) : ℕ → Pomega :=
  Function.update ρ i v
def interp : Term → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => ofNat 0
  | .succ t, ρ => succSet (interp t ρ)
  | .pred t, ρ => predSet (interp t ρ)
  | .cond z x y, ρ => condSet (interp z ρ) (interp x ρ) (interp y ρ)
  | .app u x, ρ => funOf (interp u ρ) (interp x ρ)
  | .lam i body, ρ => graph (fun v => interp body (envSet ρ i v))
def rename (i j : ℕ) : Term → Term
  | .var k => if k = i then .var j else .var k
  | .zero => .zero
  | .succ t => .succ (rename i j t)
  | .pred t => .pred (rename i j t)
  | .cond z x y => .cond (rename i j z) (rename i j x) (rename i j y)
  | .app u x => .app (rename i j u) (rename i j x)
  | .lam k body => if k = i then .lam k body else .lam k (rename i j body)
def ScottContinuousFin.Body : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Prop
  | 0, _ => True
  | n + 1, f =>
      (∀ xs : Fin n → Pomega, IsScottContinuous (fun x => f (Fin.cons x xs))) ∧
      (∀ x : Pomega, ScottContinuousFin.Body (fun xs : Fin n → Pomega => f (Fin.cons x xs)))
class ScottContinuousFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop where
  out : ScottContinuousFin.Body f
def nestApplyFin (u : Pomega) : ∀ {n : ℕ}, (Fin n → Pomega) → Pomega
  | 0, _ => u
  | _n + 1, xs => nestApplyFin (funOf u (xs 0)) (Fin.tail xs)
def curryFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Pomega
  | 0, f => f Fin.elim0
  | _n + 1, f => graph (fun x => curryFin (fun xs => f (Fin.cons x xs)))
def zeroC : Pomega := ofNat 0
def sucC : Pomega := graph succSet
def predC : Pomega := graph predSet
def condC : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => condSet z x y)))
inductive IsCombinatory : Pomega → Prop
  | zero : IsCombinatory zeroC
  | suc : IsCombinatory sucC
  | pred : IsCombinatory predC
  | cond : IsCombinatory condC
  | K : IsCombinatory Kcomb
  | S : IsCombinatory Scomb
  | app {u v} : IsCombinatory u → IsCombinatory v → IsCombinatory (funOf u v)
inductive Comb where
  | var : ℕ → Comb
  | zero | suc | pred | cond | K | S
  | app : Comb → Comb → Comb
def ofComb : Comb → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => zeroC
  | .suc, _ => sucC
  | .pred, _ => predC
  | .cond, _ => condC
  | .K, _ => Kcomb
  | .S, _ => Scomb
  | .app u v, ρ => funOf (ofComb u ρ) (ofComb v ρ)
def abs (i : ℕ) : Comb → Comb
  | .var j => if j = i then .app (.app .S .K) .K else .app .K (.var j)
  | .zero => .app .K .zero
  | .suc => .app .K .suc
  | .pred => .app .K .pred
  | .cond => .app .K .cond
  | .K => .app .K .K
  | .S => .app .K .S
  | .app u v => .app (.app .S (abs i u)) (abs i v)
def erase : Term → Comb
  | .var i => .var i
  | .zero => .zero
  | .succ t => .app .suc (erase t)
  | .pred t => .app .pred (erase t)
  | .cond z x y => .app (.app (.app .cond (erase x)) (erase y)) (erase z)
  | .app u x => .app (erase u) (erase x)
  | .lam i body => abs i (erase body)
class IsRE (u : Pomega) : Prop where
  out : REPred fun n : ℕ => n ∈ u
class ComputableFin {n : ℕ} (f : (Fin n → Pomega) → Pomega) : Prop where
  out : ScottContinuousFin f ∧ IsRE (curryFin f)
def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)
class LambdaDefinable (u : Pomega) : Prop where
  out : ∃ t : Term, interp t (fun _ => botElem) = u
def Realizes (u : Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n, funOf u (ofNat n) = ofNat (p n)
class Extensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop where
  out : ∀ n m, val n = val m → val (p n) = val (p m)
def Gpack : Pomega :=
  seq2 sucC (seq2 predC (seq2 condC (seq2 Kcomb Scomb)))
def Gcomb : Pomega :=
  graph (fun z => condSet z Gpack zeroC)
noncomputable def valNat : ℕ → Pomega :=
  Nat.strongRec fun n rec =>
    match n with
    | 0 => Gcomb
    | n + 1 =>
        rec (unpair n).1
          (Nat.lt_of_lt_of_eq
            (pair_lt_left (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n))) ⬝
        rec (unpair n).2
          (Nat.lt_of_lt_of_eq
            (pair_lt_right (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n)))
inductive GeneratedFromG : Pomega → Prop
  | G : GeneratedFromG Gcomb
  | app {u v} : GeneratedFromG u → GeneratedFromG v →
      GeneratedFromG (funOf u v)
def RE : Set Pomega := {u | IsCombinatory u}
def FUN : Set Pomega := {u | u = graph (funOf u)}
def Rcomb : Pomega := graph (fun x => seq2 (ofNat 0) x)
def Lcomb : Pomega :=
  graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)))
def barPos (u x : Pomega) : Pomega :=
  seqCons (ofNat 1) (seq2 u (funOf x (ofNat 1)))
def barStepBody (B u x : Pomega) : Pomega :=
  condSet (funOf x (ofNat 0)) (barPos u x)
    (funOf (funOf B (funOf u (funOf x (ofNat 1)))) (funOf x (ofNat 2)))
def barStep (B : Pomega) : Pomega :=
  graph (fun u => graph (fun x => barStepBody B u x))
def barComb : Pomega := fix barStep
def enumComp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))
def Gbar : Pomega := funOf barComb Gcomb
inductive GeneratedSemigroup : Pomega → Prop
  | R : GeneratedSemigroup Rcomb
  | L : GeneratedSemigroup Lcomb
  | Gbar : GeneratedSemigroup Gbar
  | comp {u v} : GeneratedSemigroup u → GeneratedSemigroup v →
      GeneratedSemigroup (enumComp u v)
def secondRecVal (u : Pomega) : Pomega :=
  graph (fun x => ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))))
def Deg (a : Pomega) : Set Pomega :=
  {u | ∃ r, IsCombinatory r ∧ u = funOf r a}
def IsSubalgebra (A : Set Pomega) : Prop :=
  Gcomb ∈ A ∧ ∀ ⦃u v⦄, u ∈ A → v ∈ A → funOf u v ∈ A
def GeneratedSubalgebra (xs : List Pomega) : Set Pomega :=
  {u | ∀ A : Set Pomega, IsSubalgebra A →
    (∀ x, x ∈ xs → x ∈ A) → u ∈ A}
class DirectedSet {α : Type u} [Preorder α] (s : Set α) : Prop where
  out : s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, x ≤ z ∧ y ≤ z
abbrev completeLatticeLE {α : Type u} [CompleteLattice α] : LE α :=
  @Preorder.toLE α
    (@PartialOrder.toPreorder α
      (@CompleteSemilatticeInf.toPartialOrder α
        (@CompleteLattice.toCompleteSemilatticeInf α ‹_›)))
abbrev completeLatticePreorder {α : Type u} [CompleteLattice α] : Preorder α :=
  @PartialOrder.toPreorder α
    (@CompleteSemilatticeInf.toPartialOrder α
      (@CompleteLattice.toCompleteSemilatticeInf α ‹_›))
abbrev completeLatticeSupSet {α : Type u} [CompleteLattice α] : SupSet α :=
  @CompleteSemilatticeSup.toSupSet α
    (@CompleteLattice.toCompleteSemilatticeSup α ‹_›)
def WayBelow {α : Type u} [CompleteLattice α] (x y : α) : Prop :=
  ∀ s : Set α, @DirectedSet α completeLatticePreorder s →
    @LE.le α completeLatticeLE y (@sSup α completeLatticeSupSet s) →
    ∃ z ∈ s, @LE.le α completeLatticeLE x z
def IsCompact {α : Type u} [CompleteLattice α] (x : α) : Prop :=
  WayBelow x x
def IsContinuousBasis {α : Type u} [CompleteLattice α]
    (basis : α → Set α) : Prop :=
  ∀ x, @DirectedSet α completeLatticePreorder (basis x) ∧
    (∀ y ∈ basis x, WayBelow y x) ∧
    x = @sSup α completeLatticeSupSet (basis x)
structure CountablyAlgebraic (α : Type u) [CompleteLattice α] where
  compact : ℕ → α
  compact_isCompact : ∀ n, IsCompact (compact n)
  compact_complete : ∀ x, IsCompact x → ∃ n, x = compact n
  density : ∀ x, x = @sSup α completeLatticeSupSet
    {k : α | IsCompact k ∧ @LE.le α completeLatticeLE k x}
def representClosure {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : Pomega :=
  {m | D.compact m ≤ sSup (D.compact '' x)}
def representClosureCode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) : Pomega :=
  graph (representClosure D)
noncomputable instance fixpointsFunOfCompleteLattice (a : Pomega) :
    CompleteLattice (Fixpoints (funOf a)) := by sorry
def retractBasis (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {y | ∃ n, e n ⊆ x ∧ (y : Pomega) = funOf a (e n)}
class Closure (a : Pomega) : Prop where
  out : Icomb ⊆ a ∧ Retract a
def compactFixedBelow (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {k | (∃ n, (k : Pomega) = funOf a (e n)) ∧ (k : Pomega) ⊆ (x : Pomega)}
def squarePair (x y : Pomega) : Pomega :=
  {k | (∃ n ∈ x, k = 2 * n) ∨ (∃ m ∈ y, k = 2 * m + 1)}
def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}
def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}
def boxTensor (a b : Pomega) : Pomega :=
  graph (fun u => squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)))
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))
def boxTag (i : ℕ) (x : Pomega) : Pomega :=
  condSet x (ofNat i) (ofNat i)
def boxPlus (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
      (squarePair (funOf (boxShift a) (squareFst u)) botElem)
      (squarePair botElem (funOf (boxShift b) (squareSnd u))))
def Vapply (a x : Pomega) : Pomega :=
  ⋂₀ {y | x ⊆ y ∧ funOf a y ⊆ y}
def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))
def ScottF : Set (Set Pomega) := {U | IsScottOpen Uᶜ}
inductive IsBooleanOpen : Set Pomega → Prop
  | ofOpen {U} : IsScottOpen U → IsBooleanOpen U
  | union {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∪ V)
  | inter {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∩ V)
  | compl {U} : IsBooleanOpen U → IsBooleanOpen Uᶜ
def ScottB : Set (Set Pomega) := {U | IsBooleanOpen U}
def IsScottGdelta (U : Set Pomega) : Prop :=
  ∃ Us : ℕ → Set Pomega, (∀ n, IsScottOpen (Us n)) ∧ U = ⋂ n, Us n
def IsFcapG (U : Set Pomega) : Prop :=
  ∃ C O, IsScottOpen Cᶜ ∧ IsScottOpen O ∧ U = C ∩ O
def IsFcapGdelta (U : Set Pomega) : Prop :=
  ∃ C G, IsScottOpen Cᶜ ∧ IsScottGdelta G ∧ U = C ∩ G
def IsBdelta (U : Set Pomega) : Prop :=
  ∃ Bs : ℕ → Set Pomega, (∀ n, IsBooleanOpen (Bs n)) ∧ U = ⋂ n, Bs n
structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z
namespace RestrictedEquiv
def mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x
def arrowE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun f g =>
    f = graph (fun x => funOf f x) ∧
      g = graph (fun x => funOf g x) ∧
        ∀ x y, A.rel x y → B.rel (funOf f x) (funOf g y)
  symm := by sorry
  trans := by sorry
def prodE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
      v = pairElem (funOf v (ofNat 0)) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 0)) (funOf v (ofNat 0)) ∧
          B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))
  symm := by sorry
  trans := by sorry
theorem seq2_tag_ne (x y : Pomega) :
    seq2 (ofNat 0) x ≠ seq2 (ofNat 1) y := by sorry
theorem pairElem_tag_ne (x y : Pomega) :
    pairElem (ofNat 0) x ≠ pairElem (ofNat 1) y :=
  seq2_tag_ne x y
def sumE (A B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun u v =>
    (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 0) (funOf v (ofNat 1)) ∧
        A.rel (funOf u (ofNat 1)) (funOf v (ofNat 1))) ∨
      (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
        v = pairElem (ofNat 1) (funOf v (ofNat 1)) ∧
        B.rel (funOf u (ofNat 1)) (funOf v (ofNat 1)))
  symm := by sorry
  trans := by sorry
def Ea (a : Pomega) : RestrictedEquiv where
  rel := fun x y => typed x a ∧ typed y a ∧ x = y
  symm := by sorry
  trans := by sorry
end RestrictedEquiv
open RestrictedEquiv
def Z : ℕ → Pomega → Pomega → Pomega
  | 0, _, x => x
  | n + 1, f, x => funOf f (Z n f x)
def Zcomb (n : ℕ) : Pomega :=
  graph (fun f => graph (fun x => Z n f x))
theorem theorem_1_1 (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by sorry
theorem theorem_1_2 {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) := by sorry
theorem theorem_1_3 {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) := by sorry
namespace theorem_1_3
theorem tuple {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {g h : Pomega → Pomega} (hg : IsScottContinuous g) (hh : IsScottContinuous h) :
    IsScottContinuous (fun x => f (g x) (h x)) := by sorry
end theorem_1_3
namespace theorem_1_3
theorem nary {f : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z))
    {g h i : Pomega → Pomega}
    (hg : IsScottContinuous g) (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun x => f (g x) (h x) (i x)) := by sorry
end theorem_1_3
def closureCompact (a : Pomega) (ha : Closure a) (n : ℕ) :
    Fixpoints (funOf a) :=
  ⟨funOf a (e n), by sorry⟩
theorem theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by sorry
theorem theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by sorry
namespace theorem_1_5
theorem extension {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (hf : Continuous f) (x : X) :
    extend (Y := Y) (X := X) f ↑x = f x := by sorry
end theorem_1_5
theorem theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsEmbedding (embed U) where
  toIsInducing := sorry
  injective := sorry
theorem theorem_2_1 (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by sorry
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    (∀ j, (∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) →
        interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ) ∧
      funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) ∧
        ∀ σ, (∀ v, interp body (envSet ρ i v) = interp σ (envSet ρ i v)) →
          interp (.lam i body) ρ = interp (.lam i σ) ρ := by sorry
theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs := by sorry
theorem theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb := by sorry
namespace theorem_2_4
theorem complete (t : Term) (ρ : ℕ → Pomega) :
    interp t ρ = ofComb (erase t) ρ := by sorry
end theorem_2_4
theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by sorry
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsRE (graph f) ↔ IsCombinatory (graph f)) ∧
      (LambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by sorry
namespace theorem_2_6
theorem fin {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) :
    (ComputableFin f ↔ IsRE (curryFin f)) ∧
      (IsRE (curryFin f) ↔ IsCombinatory (curryFin f)) ∧
      (LambdaDefinable (curryFin f) ↔ IsCombinatory (curryFin f)) := by sorry
end theorem_2_6
theorem theorem_3_1 {u : Pomega} :
    IsCombinatory u ↔ GeneratedFromG u := by sorry
theorem theorem_3_2 :
    (∀ n, valNat n ∈ RE) ∧
      valNat 0 = Gcomb ∧
        (∀ n m, valNat (applyNat n m) = funOf (valNat n) (valNat m)) := by sorry
namespace theorem_3_2
theorem range : RE = Set.range valNat := by sorry
end theorem_3_2
theorem theorem_3_3 :
    ∃ v : ℕ → ℕ, Primrec v ∧
      Primrec (recNat v) ∧
      (∀ n, valNat (v n) = secondRecVal (valNat n)) ∧
      (∀ n, recNat v n = applyNat (v n) (num (v n))) ∧
      ∀ n, valNat (recNat v n) =
        funOf (valNat n) (ofNat (recNat v n)) := by sorry
theorem theorem_3_4 :
    ¬ IsRE {n | valNat n = botElem} := by sorry
theorem theorem_3_5 {p : ℕ → ℕ}
    (hp : ∃ u, IsCombinatory u ∧ Realizes u p)
    (hext : Extensional valNat p) :
    ∃ q, IsCombinatory q ∧ ∀ n, valNat (p n) = funOf q (valNat n) := by sorry
theorem theorem_3_6 (A : Set Pomega) :
    (∃ a, A = Deg a) ↔
      ∃ xs : List Pomega, A = GeneratedSubalgebra xs := by sorry
theorem theorem_3_7 {u : Pomega} :
    u ∈ RE ∩ FUN ↔ GeneratedSemigroup u := by sorry
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (_ha : Retract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          ∀ x : Fixpoints (funOf a),
            DirectedSubset (retractBasis a x) ∧
              (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by sorry
namespace theorem_4_1
theorem continuous {a : Pomega} (ha : Retract a) :
    ∀ x : Fixpoints (funOf a),
      DirectedSubset (retractBasis a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) ∧
        ∀ y ∈ retractBasis a x,
          ∀ s : Set (Fixpoints (funOf a)),
            DirectedSubset s →
              (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
              ∃ z ∈ s, (y : Pomega) ⊆ z := by sorry
end theorem_4_1
theorem theorem_4_2 {a b c : Pomega} :
    (Retract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by sorry
theorem theorem_4_3 {a b a' b' c : Pomega}
    (ha : Retract a) (hb : Retract b) (_ha' : Retract a')
    (_hb' : Retract b') (hc : Retract c) :
    Retract (arrowR a b) ∧
      (IsStrict b → IsStrict (arrowR a b)) ∧
      (∀ u, typed u (arrowR a b) ↔
        u = comp u a ∧ ∀ x, typed x a → typed (funOf u x) b) ∧
      (retractLe a a' → retractLe b b' →
        retractLe (arrowR a b) (arrowR a' b')) ∧
      (∀ f f', typed f (arrowR a b) → typed f' (arrowR a' b') →
        typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b'))) ∧
      (∀ f f', typed f (arrowR a b) → typed f' (arrowR b c) →
        typed (comp f' f) (arrowR a c)) := by sorry
theorem theorem_4_4 :
    (∀ x y, funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y) ∧
      Retract botElem := by sorry
namespace theorem_4_4
theorem typed_iff {a b u : Pomega} :
    typed u (tensorR a b) ↔
      u = pairSeq (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
        typed (funOf u (ofNat 0)) a ∧ typed (funOf u (ofNat 1)) b := by sorry
end theorem_4_4
namespace tensorR
theorem isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (tensorR a b) := by sorry
end tensorR
theorem theorem_4_5 (a b : Pomega) :
    dcondSet botElem
        (pairSeq (ofNat 0) (funOf a botElem))
        (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      Retract botElem := by sorry
namespace theorem_4_5
theorem sum {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (plusR a b) ∧ IsStrict (plusR a b) ∧
      (∀ u, typed u (plusR a b) ↔
        u = botElem ∨ u = topElem ∨
          (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
            (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b)) := by sorry
end theorem_4_5
theorem theorem_4_6 {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    ((∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F))) ∧
      Nonempty (Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F) := by sorry
namespace theorem_4_6
theorem Limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a)) :
    (∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F)) := by sorry
end theorem_4_6
theorem theorem_5_1 {a : Pomega} (ha : Closure a) :
    (∀ x : Fixpoints (funOf a),
      IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n) ∧
    ∀ x : Fixpoints (funOf a),
      DirectedSubset (compactFixedBelow a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' compactFixedBelow a x) := by sorry
theorem theorem_5_2 {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) ∧
      Closure (representClosureCode D) ∧
      ∃ φ : α → Fixpoints (funOf (representClosureCode D)),
        Function.Bijective φ ∧
          ∀ x y, x ≤ y ↔ (φ x : Pomega) ⊆ φ y := by sorry
theorem theorem_5_3 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Retract (arrowR a b) := by sorry
namespace theorem_5_3
theorem closure {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (arrowR a b) := by sorry
end theorem_5_3
namespace theorem_5_4
theorem times {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxTensor a b) := by sorry
theorem plus {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxPlus a b) := by sorry
end theorem_5_4
theorem theorem_5_4 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxTensor a b) ∧ Closure (boxPlus a b) := by sorry
namespace boxPlus
theorem typed_iff {a b u : Pomega} (ha : Retract a) (hb : Retract b) :
    typed u (boxPlus a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = squarePair x botElem ∧ typed x (boxShift a)) ∨
          (∃ y, u = squarePair botElem y ∧ typed y (boxShift b)) := by sorry
end boxPlus
theorem theorem_5_5.universe :
    Closure Vcomb ∧ ∀ a, Closure a ↔ typed a Vcomb := by sorry
theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by sorry
theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by sorry
theorem theorem_6_2 :
    ∀ U, U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = botElem} := by sorry
theorem theorem_6_3 :
    ∀ U, IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = topElem} := by sorry
theorem theorem_6_4 :
    ∀ U, IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = ofNat 0} := by sorry
theorem theorem_6_5 :
    ∀ U, IsFcapGdelta U ↔
      ∃ f, IsScottContinuous f ∧ U = {x | f x = succSet topElem} := by sorry
theorem theorem_6_6 :
    ∀ U, U ∈ ScottB ↔
      ∃ f, IsScottContinuous f ∧ ∃ E : Set Pomega,
        E.Finite ∧ (∀ e ∈ E, e.Finite) ∧ U = {x | f x ∈ E} := by sorry
theorem theorem_6_7 :
    ∀ U, IsBdelta U ↔
      ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x} := by sorry
theorem theorem_7_1 (A B : RestrictedEquiv) :
    (∀ f, (arrowE A B).mem f ↔
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ {f x}, (arrowE A B).mem f → A.mem x → B.mem (funOf f x)) ∧
      (∀ u, (prodE A B).mem u ↔
        u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u ↔
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by sorry
theorem theorem_7_2 {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    (∀ x y, funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y)) ∧
      (∀ f g, (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
        ((arrowE (Ea a) (Ea b)).rel f g →
          (Ea (arrowR a b)).rel (funOf (arrowR a b) f)
            (funOf (arrowR a b) g)) ∧
        ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g)) ∧
      (∀ u v, (Ea (tensorR a b)).rel u v ↔ (prodE (Ea a) (Ea b)).rel u v) ∧
      (∀ u v, (Ea (plusR a b)).rel u v ↔
        (sumE (Ea a) (Ea b)).rel u v ∨
          (u = botElem ∧ v = botElem) ∨ (u = topElem ∧ v = topElem)) := by sorry
theorem theorem_7_3 :
    (∀ A, (arrowE A A).mem Icomb) ∧
      (∀ A B, (arrowE A (arrowE B A)).mem Kcomb) ∧
      (∀ A B C,
        (arrowE (arrowE A (arrowE B C))
          (arrowE (arrowE A B) (arrowE A C))).mem Scomb) ∧
      (∀ i, (∀ A, (arrowE A A).mem i) → i = Icomb) ∧
      (∀ k, (∀ A B, (arrowE A (arrowE B A)).mem k) → k = Kcomb) ∧
      (∀ s,
        (∀ f, funOf s f =
          funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y)))) →
        (∀ f g, funOf (funOf s f) g =
          funOf (funOf s f) (graph (fun x => funOf g x))) →
        (∀ A B C,
          (arrowE (arrowE A (arrowE B C))
            (arrowE (arrowE A B) (arrowE A C))).mem s) →
        s = Scomb) := by sorry
theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n := by sorry
end DomainTheory.DataTypesAsLattices
