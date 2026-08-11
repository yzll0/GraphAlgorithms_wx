/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.SimplePath

/-!
# Simple cycles

A `SimpleCycle α` is a closed `SimpleWalk α` of length at least three whose
interior (the walk with its final repeated vertex dropped) is a simple path.
It is represented as a subtype of `SimpleWalk`.

The length-≥-3 bound is the *undirected* convention; the directed notion
(which admits length-two cycles) will get its own `SimpleDiCycle`. The `arcs`
API here only reflects a chosen traversal orientation and is not canonical.

## Main definitions

* `SimpleWalk.IsCycle` — a closed simple walk whose dropped-tail walk is a path.
* `SimpleCycle` — a simple walk bundled with a proof of `SimpleWalk.IsCycle`.
* `SimpleCycle.interior` — the simple path obtained by dropping the repeated endpoint.
* `SimpleCycle.reverse`, `SimpleCycle.reroot` — change the chosen traversal or root.
* `SimpleCycle.ofPathClosing` — close one path to form a cycle.
* `SimpleCycle.ofTwoPaths` — select a cycle from two distinct paths with common endpoints.

## Main results

* `SimpleCycle.edges_nodup` — a simple cycle traverses no edge twice.
* `SimpleCycle.length_ofTwoPaths` — the selected cycle is no longer than the input paths.
* `SimpleCycle.head_ofTwoPaths_mem_left` — the selected root lies on the first path.
* `SimpleCycle.edges_ofTwoPaths_subset` — every selected edge comes from an input path.
-/

variable {α : Type*}

namespace SimpleWalk

/-- A simple walk is a cycle when it is closed, has length at least three,
and its dropped-tail walk is a path. -/
@[grind] def IsCycle (w : SimpleWalk α) : Prop :=
  3 ≤ w.length ∧ w.closed ∧ w.dropTail.nodup

namespace IsCycle

/-- Reversal preserves the simple-cycle property. -/
lemma reverse (w : SimpleWalk α) (h : IsCycle w) :
    IsCycle w.reverse := by
  obtain ⟨hlen, hclosed, hnodup⟩ := h
  exact ⟨by simpa using hlen, by simpa [VertexSeq.closed] using hclosed.symm,
    VertexSeq.nodup_reverse_dropTail_of_closed w.val hclosed hnodup⟩

end IsCycle

end SimpleWalk

/-- A simple cycle is a simple walk that is a cycle. -/
def SimpleCycle (α : Type*) :=
  { w : SimpleWalk α // SimpleWalk.IsCycle w }

namespace SimpleCycle

/-! ## Basic accessors -/

/-- The underlying simple walk. -/
abbrev val (c : SimpleCycle α) : SimpleWalk α := c.1

/-- The underlying vertex sequence. -/
abbrev vertices (c : SimpleCycle α) : VertexSeq α := c.val.val

/-- The list of vertices visited by the cycle. -/
abbrev support (c : SimpleCycle α) : List α := (vertices c).toList

/-- The unordered edges traversed by the cycle. -/
abbrev edges (c : SimpleCycle α) : List (Sym2 α) := (vertices c).edges

/-- The directed arcs traversed by the cycle. -/
abbrev arcs (c : SimpleCycle α) : List (α × α) := (vertices c).arcs

/-- The first vertex of the cycle. -/
abbrev head (c : SimpleCycle α) : α := (vertices c).head

/-- The last vertex of the cycle (equal to its head, since a cycle is closed). -/
abbrev tail (c : SimpleCycle α) : α := (vertices c).tail

/-- The number of edges in the cycle. -/
abbrev length (c : SimpleCycle α) : ℕ := (vertices c).length

/-- A cycle is closed: its first and last vertex coincide. -/
lemma closed (c : SimpleCycle α) : c.val.closed := c.2.2.1

/-- A simple cycle is, in particular, a simple walk. -/
instance : Coe (SimpleCycle α) (SimpleWalk α) :=
  ⟨val⟩

/-! ## interior -/

/-- The interior of the cycle: the vertex sequence with its final (repeated)
vertex dropped. -/
def interior (c : SimpleCycle α) : SimplePath α :=
  ⟨c.val.dropTail, c.2.2.2⟩

attribute [simp, grind] SimpleCycle.val SimpleCycle.vertices SimpleCycle.support
  SimpleCycle.edges SimpleCycle.arcs SimpleCycle.head SimpleCycle.tail SimpleCycle.length
  SimpleCycle.interior

/-! ## Constructors -/

/-! ### ofPathClosing -/

/-- The simple walk obtained by appending the starting vertex to a path of
length at least two. -/
private def walkOfPathClosing (p : SimplePath α) (hlen : 2 ≤ p.vertices.length) :
    SimpleWalk α :=
  ⟨VertexSeq.cons p.vertices p.head, ⟨p.val.nonstalling, fun h => by
    have hzero := VertexSeq.length_zero_of_nodup_closed p.vertices p.nodup
      (show p.vertices.closed from h.symm)
    omega⟩⟩

/-- Closing a path of length at least two satisfies the cycle conditions. -/
private lemma isCycle_ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ p.vertices.length) :
    SimpleWalk.IsCycle (walkOfPathClosing p hlen) := by
  change 3 ≤ (VertexSeq.cons p.vertices p.head).length ∧
    (VertexSeq.cons p.vertices p.head).closed ∧
    (VertexSeq.cons p.vertices p.head).dropTail.nodup
  refine ⟨?_, by simp [VertexSeq.closed], by simpa using p.nodup⟩
  simp [VertexSeq.length] at hlen ⊢
  omega

/-- Close a simple path by adding an edge from its tail back to its head. -/
def ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ (SimplePath.vertices p).length) :
    SimpleCycle α :=
  ⟨walkOfPathClosing p hlen, isCycle_ofPathClosing p hlen⟩

/-- Closing a path adds exactly one edge. -/
@[simp] lemma length_ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ p.length) :
    (ofPathClosing p hlen).length = p.length + 1 := by
  change 1 + p.length = p.length + 1
  omega

/-- Closing a path preserves its head. -/
@[simp] lemma head_ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ p.length) :
    (ofPathClosing p hlen).head = p.head := by
  rfl

/-- The edges of a closed path are the path edges followed by its closing edge. -/
lemma edges_ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ p.length) :
    (ofPathClosing p hlen).edges =
      p.edges ++ [s(p.tail, p.head)] := by
  simp [ofPathClosing, walkOfPathClosing, VertexSeq.edges_cons,
    List.concat_eq_append]

/-! ### ofTwoPaths -/

/-- Two paths with the same tail can be glued after reversing the second one. -/
private lemma tail_eq_head_reverse_of_tail_eq (P Q : SimplePath α)
    (htail : P.tail = Q.tail) : P.val.tail = Q.val.reverse.head := by
  simpa using htail

/-- The vertex where two paths with a common head diverge: the last vertex of the
longest common prefix of their vertex lists.

Defined via `List.commonPrefix`, so no index arithmetic is involved. Compare the
earlier `findIdx`-on-`zip` definition, which forced every downstream lemma to
carry dependent `getElem` bounds. -/
private def divergenceVertex [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) : α :=
  (List.commonPrefix p.vertices.toList q.vertices.toList).getLast
    (List.commonPrefix_ne_nil (x := p.head) (by grind) (by grind))

/-- The three facts that make the divergence vertex what it is: the two suffixes
from it end together, it is not that common endpoint, and the two paths take
different next steps out of it. -/
private lemma divergenceVertex_core [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    let a := divergenceVertex p q hhead
    ∃ hap : a ∈ p.vertices, ∃ haq : a ∈ q.vertices,
      (p.suffixFrom a hap).tail = (q.suffixFrom a haq).tail ∧
      a ≠ (p.suffixFrom a hap).tail ∧
      (p.suffixFrom a hap).vertices.dropHead.head ≠
        (q.suffixFrom a haq).vertices.dropHead.head := by
  classical
  have hnp : p.vertices.toList.Nodup := (VertexSeq.nodup_iff_toList_nodup _).1 p.nodup
  have hnq : q.vertices.toList.Nodup := (VertexSeq.nodup_iff_toList_nodup _).1 q.nodup
  obtain ⟨r₁, r₂, h₁, h₂, hdiff⟩ :=
    List.commonPrefix_split p.vertices.toList q.vertices.toList
  have hcne : List.commonPrefix p.vertices.toList q.vertices.toList ≠ [] :=
    List.commonPrefix_ne_nil (x := p.head) (by grind) (by grind)
  set c := List.commonPrefix p.vertices.toList q.vertices.toList with hc
  set a := divergenceVertex p q hhead with hadefa
  have hadef : a = c.getLast hcne := rfl
  have hsplitc : c.dropLast ++ [a] = c := by
    rw [hadef]; exact List.dropLast_append_getLast hcne
  have hlp : p.vertices.toList = c.dropLast ++ a :: r₁ := by grind
  have hlq : q.vertices.toList = c.dropLast ++ a :: r₂ := by grind
  have hap : a ∈ p.vertices := by grind
  have haq : a ∈ q.vertices := by grind
  have hsp : (p.vertices.suffixFrom a hap).toList = a :: r₁ :=
    VertexSeq.toList_suffixFrom_eq_of_split _ p.nodup a hap _ _ hlp
  have hsq : (q.vertices.suffixFrom a haq).toList = a :: r₂ :=
    VertexSeq.toList_suffixFrom_eq_of_split _ q.nodup a haq _ _ hlq
  -- Each path ends at the last entry of its own `a :: rᵢ`; establish this once.
  have htp : p.vertices.tail = (a :: r₁).getLast (by simp) := by
    rw [← VertexSeq.getLast_toList p.vertices (by grind)]
    grind
  have htq : q.vertices.tail = (a :: r₂).getLast (by simp) := by
    rw [← VertexSeq.getLast_toList q.vertices (by grind)]
    grind
  -- Both remainders are non-empty: otherwise one vertex list is a prefix of the
  -- other, and a shared last vertex plus `nodup` would force the two paths to be
  -- equal, contradicting `hne`.
  have hr₁ : r₁ ≠ [] := by
    rintro rfl
    have hr₂ : r₂ = [] := by
      rcases r₂ with _ | ⟨y, ys⟩
      · rfl
      · exfalso
        have hmem := List.getLast_mem (l := y :: ys) (by simp)
        grind [List.getLast_cons, List.nodup_append]
    exact hne (VertexSeq.toList_injective (by grind))
  have hr₂ : r₂ ≠ [] := by
    rintro rfl
    have hmem := List.getLast_mem (l := r₁) hr₁
    grind [List.getLast_cons, List.nodup_append]
  have hane : a ∉ r₁ := by grind [List.nodup_append]
  refine ⟨hap, haq, by grind [VertexSeq.tail_suffixFrom], ?_, ?_⟩
  · have hmem := List.getLast_mem (l := r₁) hr₁
    grind [VertexSeq.tail_suffixFrom, List.getLast_cons]
  · have hd₁ := VertexSeq.head_dropHead_of_toList_eq_cons_cons _ a (r₁.head hr₁) r₁.tail
      (by rw [hsp, List.cons_head_tail hr₁])
    have hd₂ := VertexSeq.head_dropHead_of_toList_eq_cons_cons _ a (r₂.head hr₂) r₂.tail
      (by rw [hsq, List.cons_head_tail hr₂])
    have := hdiff (r₁.head hr₁) (by grind [List.head?_eq_some_head]) (r₂.head hr₂)
      (by grind [List.head?_eq_some_head])
    grind

/-- The full divergence specification used by `buildOfTwoPaths`. The four extra
components are routine consequences of `divergenceVertex_core`. -/
private lemma divergenceVertex_spec [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    let a := divergenceVertex p q hhead
    ∃ hap : a ∈ p.vertices, ∃ haq : a ∈ q.vertices,
      let p' := p.suffixFrom a hap
      let q' := q.suffixFrom a haq
      p'.head = a ∧ q'.head = a ∧ p'.tail = q'.tail ∧
        p'.length ≠ 0 ∧ q'.length ≠ 0 ∧ a ≠ p'.tail ∧
        p'.vertices.dropHead.head ≠ q'.vertices.dropHead.head := by
  obtain ⟨hap, haq, htaileq, hane, hsecond⟩ := divergenceVertex_core p q hhead htail hne
  refine ⟨hap, haq, ?_, ?_, htaileq, ?_, ?_, hane, hsecond⟩ <;>
    grind [VertexSeq.head_suffixFrom]

private lemma divergenceVertex_mem_left [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    divergenceVertex p q hhead ∈ p.vertices :=
  (divergenceVertex_core p q hhead htail hne).1

private lemma divergenceVertex_mem_right [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    divergenceVertex p q hhead ∈ q.vertices :=
  (divergenceVertex_core p q hhead htail hne).2.1

/-! #### Divergence context -/

/-- The data shared by every step of the `ofTwoPaths` construction: the
divergence vertex `a` with the facts about the two suffixes `p.suffixFrom a`,
`q.suffixFrom a` that the later steps consume. Bundled once (via `divergenceData`)
so no helper re-derives `divergenceVertex_spec`. -/
private structure DivergenceData [DecidableEq α] (p q : SimplePath α) where
  vertex : α
  mem_left : vertex ∈ p.vertices
  mem_right : vertex ∈ q.vertices
  head_left : (p.suffixFrom vertex mem_left).head = vertex
  head_right : (q.suffixFrom vertex mem_right).head = vertex
  tail_eq : (p.suffixFrom vertex mem_left).tail = (q.suffixFrom vertex mem_right).tail
  length_left : (p.suffixFrom vertex mem_left).length ≠ 0
  length_right : (q.suffixFrom vertex mem_right).length ≠ 0
  second_ne : (p.suffixFrom vertex mem_left).vertices.dropHead.head ≠
    (q.suffixFrom vertex mem_right).vertices.dropHead.head

/-- Extract the divergence context from two distinct paths with common endpoints. -/
private def divergenceData [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) : DivergenceData p q :=
  let a := divergenceVertex p q hhead
  let hap := divergenceVertex_mem_left p q hhead htail hne
  let haq := divergenceVertex_mem_right p q hhead htail hne
  have hspec : (p.suffixFrom a hap).head = a ∧ (q.suffixFrom a haq).head = a ∧
      (p.suffixFrom a hap).tail = (q.suffixFrom a haq).tail ∧
      (p.suffixFrom a hap).length ≠ 0 ∧ (q.suffixFrom a haq).length ≠ 0 ∧
      a ≠ (p.suffixFrom a hap).tail ∧
      (p.suffixFrom a hap).vertices.dropHead.head ≠
        (q.suffixFrom a haq).vertices.dropHead.head := by
    obtain ⟨hap', haq', h⟩ := divergenceVertex_spec p q hhead htail hne
    simpa [a, hap, haq] using h
  ⟨a, hap, haq, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2.1,
    hspec.2.2.2.2.2.2⟩

/-! #### The interior walk -/

/-- The interior of the closed walk `p' ⋯ (q')⁻¹`: drop both copies of the
divergence vertex. Its endpoints are the two distinct vertices right after the
divergence vertex on `p` and on `q`. -/
private def interiorWalk [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : SimpleWalk α :=
  ((p.suffixFrom d.vertex d.mem_left).val.glue
      (q.suffixFrom d.vertex d.mem_right).val.reverse
      (tail_eq_head_reverse_of_tail_eq _ _ d.tail_eq)).dropHead.dropTail

/-- The interior walk starts at the vertex right after the divergence vertex on `p`. -/
private lemma head_interiorWalk [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) :
    (interiorWalk d).head = (p.suffixFrom d.vertex d.mem_left).vertices.dropHead.head := by
  have hpPos := d.length_left
  change ((p.suffixFrom d.vertex d.mem_left).val.glue
    (q.suffixFrom d.vertex d.mem_right).val.reverse _).val.dropHead.dropTail.head = _
  rw [VertexSeq.head_dropTail]
  exact SimpleWalk.head_dropHead_glue _ _ _ hpPos

/-- The interior walk ends at the vertex right after the divergence vertex on `q`. -/
private lemma tail_interiorWalk [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) :
    (interiorWalk d).tail = (q.suffixFrom d.vertex d.mem_right).vertices.dropHead.head := by
  have hpPos := d.length_left
  have hqPos := d.length_right
  set W : SimpleWalk α := (p.suffixFrom d.vertex d.mem_left).val.glue
    (q.suffixFrom d.vertex d.mem_right).val.reverse
    (tail_eq_head_reverse_of_tail_eq _ _ d.tail_eq) with hW
  have hWLen : W.length = (p.suffixFrom d.vertex d.mem_left).length +
      (q.suffixFrom d.vertex d.mem_right).length := by rw [hW]; simp
  have hW2 : 2 ≤ W.val.length := by
    have h2 : 2 ≤ W.length := by omega
    simpa using h2
  change W.val.dropHead.dropTail.tail = (q.suffixFrom d.vertex d.mem_right).vertices.dropHead.head
  rw [VertexSeq.tail_dropTail_dropHead _ hW2]
  simp only [hW, SimpleWalk.glue, dif_neg hpPos]
  rw [VertexSeq.dropTail_append _ _ (by simpa using hqPos), VertexSeq.tail_append]
  change (q.suffixFrom d.vertex d.mem_right).vertices.reverse.dropTail.tail =
    (q.suffixFrom d.vertex d.mem_right).vertices.dropHead.head
  rw [VertexSeq.dropTail_reverse, VertexSeq.tail_reverse]

/-- The interior walk is two edges shorter than the closed walk. -/
private lemma length_interiorWalk [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) :
    (interiorWalk d).length + 2 =
      (p.suffixFrom d.vertex d.mem_left).length + (q.suffixFrom d.vertex d.mem_right).length := by
  have hpPos := d.length_left
  have hqPos := d.length_right
  set W : SimpleWalk α := (p.suffixFrom d.vertex d.mem_left).val.glue
    (q.suffixFrom d.vertex d.mem_right).val.reverse
    (tail_eq_head_reverse_of_tail_eq _ _ d.tail_eq) with hW
  have hWLen : W.length = (p.suffixFrom d.vertex d.mem_left).length +
      (q.suffixFrom d.vertex d.mem_right).length := by rw [hW]; simp
  have h2v : 2 ≤ W.val.length := by
    have h2 : 2 ≤ W.length := by omega
    simpa using h2
  have hWPos : W.val.length ≠ 0 := by omega
  have hDropHead := VertexSeq.length_dropHead_succ W.val hWPos
  have hDropHeadPos : W.val.dropHead.length ≠ 0 := by omega
  have hDropTail := VertexSeq.length_dropTail_succ W.val.dropHead hDropHeadPos
  have hIW : (interiorWalk d).length + 2 = W.length := by
    change W.val.dropHead.dropTail.length + 2 = W.val.length
    omega
  omega

/-- The divergence vertex does not lie in the interior walk: it occurs in the
closed walk only at the two endpoints, both of which were dropped. -/
private lemma not_mem_interiorWalk [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : d.vertex ∉ (interiorWalk d).val := by
  have hpPos := d.length_left
  have hqPos := d.length_right
  have hpHead := d.head_left
  have hqHead := d.head_right
  set p' := p.suffixFrom d.vertex d.mem_left with hp'
  set q' := q.suffixFrom d.vertex d.mem_right with hq'
  have hqNot : d.vertex ∉ q'.vertices.reverse.dropTail := by
    simpa [hqHead] using VertexSeq.tail_not_mem_dropTail_of_nodup q'.vertices.reverse
      (VertexSeq.nodup_reverse q'.vertices q'.nodup) (by simpa using hqPos)
  intro ha
  change d.vertex ∈ ((p'.val.glue q'.val.reverse
    (tail_eq_head_reverse_of_tail_eq _ _ d.tail_eq)).dropHead.dropTail).val at ha
  simp only [SimpleWalk.glue, dif_neg hpPos] at ha
  by_cases hp1 : p'.length = 1
  · have hpDropEq : p'.vertices.dropTail = VertexSeq.singleton d.vertex := by
      have hz : p'.vertices.dropTail.length = 0 := by
        have := VertexSeq.length_dropTail_succ p'.vertices hpPos
        change p'.vertices.length = 1 at hp1; omega
      rw [VertexSeq.eq_singleton_of_length_zero _ hz]; simp [hpHead]
    change d.vertex ∈
      (p'.vertices.dropTail.append q'.vertices.reverse).dropHead.dropTail at ha
    rw [hpDropEq, VertexSeq.dropHead_singleton_append] at ha
    exact hqNot ha
  · have hpNot : d.vertex ∉ p'.vertices.dropTail.dropHead := by
      have hpos : p'.vertices.dropTail.length ≠ 0 := by
        have := VertexSeq.length_dropTail_succ p'.vertices hpPos
        change p'.vertices.length ≠ 1 at hp1; omega
      simpa [hpHead] using VertexSeq.head_not_mem_dropHead_of_nodup p'.vertices.dropTail
        (VertexSeq.nodup_dropTail p'.vertices p'.nodup) hpos
    rcases VertexSeq.mem_dropTail_dropHead_append _ _ _ ha with haP | haQ
    · exact hpNot haP
    · exact hqNot haQ

/-- Every edge of the interior walk is traversed by one of the two paths. -/
private lemma edges_interiorWalk_subset [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) {e : Sym2 α} (he : e ∈ (interiorWalk d).edges) :
    e ∈ p.edges ∨ e ∈ q.edges := by
  set p' := p.suffixFrom d.vertex d.mem_left with hp'
  set q' := q.suffixFrom d.vertex d.mem_right with hq'
  set W : SimpleWalk α := p'.val.glue q'.val.reverse
    (tail_eq_head_reverse_of_tail_eq _ _ d.tail_eq) with hW
  change e ∈ (W.dropHead.dropTail).edges at he
  have heW : e ∈ W.edges :=
    SimpleWalk.edges_dropHead_subset W (SimpleWalk.edges_dropTail_subset W.dropHead he)
  rcases (show e ∈ p'.edges ∨ e ∈ q'.val.reverse.edges by
    simpa [hW, SimpleWalk.edges_glue] using heW) with heP | heQ
  · exact Or.inl (SimplePath.edges_suffixFrom_subset p d.vertex d.mem_left heP)
  · exact Or.inr (SimplePath.edges_suffixFrom_subset q d.vertex d.mem_right (by simpa using heQ))

/-! #### The loop-erased interior -/

/-- Loop-erase the interior walk to a simple path running between the two
vertices adjacent to the divergence vertex. -/
private def erasedInterior [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : SimplePath α :=
  SimplePath.cycleErase (interiorWalk d)

private lemma head_erasedInterior [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) :
    (erasedInterior d).head = (p.suffixFrom d.vertex d.mem_left).vertices.dropHead.head := by
  change (interiorWalk d).val.cycleErase.head = _
  exact (VertexSeq.head_cycleErase (interiorWalk d).val).trans (head_interiorWalk d)

private lemma tail_erasedInterior [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) :
    (erasedInterior d).tail = (q.suffixFrom d.vertex d.mem_right).vertices.dropHead.head := by
  change (interiorWalk d).val.cycleErase.tail = _
  exact (VertexSeq.tail_cycleErase (interiorWalk d).val).trans (tail_interiorWalk d)

/-- The loop-erased interior is non-trivial: its endpoints are distinct. -/
private lemma length_erasedInterior_ne_zero [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : (erasedInterior d).length ≠ 0 := by
  intro hzero
  exact d.second_ne ((head_erasedInterior d).symm.trans
    ((VertexSeq.head_eq_tail_of_length_zero _ hzero).trans (tail_erasedInterior d)))

private lemma length_erasedInterior_le [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : (erasedInterior d).length ≤ (interiorWalk d).length :=
  VertexSeq.length_cycleErase_le (interiorWalk d).val

/-- The divergence vertex is disjoint from the loop-erased interior. -/
private lemma not_mem_erasedInterior [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : d.vertex ∉ (erasedInterior d).vertices := by
  intro haT
  exact not_mem_interiorWalk d (VertexSeq.cycleErase_subset (interiorWalk d).val d.vertex haT)

private lemma edges_erasedInterior_subset [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) {e : Sym2 α} (he : e ∈ (erasedInterior d).edges) :
    e ∈ p.edges ∨ e ∈ q.edges :=
  edges_interiorWalk_subset d (SimpleWalk.edges_cycleErase_subset (interiorWalk d) he)

/-! #### Prepending the divergence vertex -/

/-- Prepend the divergence vertex to the loop-erased interior. The vertex is
disjoint from that interior, so the result is still a simple path. -/
private def pathOfTwoPaths [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : SimplePath α :=
  (SimplePath.singleton d.vertex).append (erasedInterior d) (by
    intro z hzA hzT
    change z ∈ VertexSeq.singleton d.vertex at hzA
    have hz : z = d.vertex := VertexSeq.mem_singleton.mp hzA
    subst z
    exact not_mem_erasedInterior d hzT)

private lemma head_pathOfTwoPaths [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : (pathOfTwoPaths d).head = d.vertex := by
  simp [pathOfTwoPaths]

private lemma tail_pathOfTwoPaths [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : (pathOfTwoPaths d).tail = (erasedInterior d).tail := by
  simp [pathOfTwoPaths]

private lemma length_pathOfTwoPaths [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : (pathOfTwoPaths d).length = (erasedInterior d).length + 1 := by
  simp [pathOfTwoPaths, VertexSeq.length_append]

private lemma two_le_length_pathOfTwoPaths [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) : 2 ≤ (pathOfTwoPaths d).length := by
  have h := length_pathOfTwoPaths d
  have := length_erasedInterior_ne_zero d
  omega

/-- Every edge of the prepended path comes from one of the two input paths: the
joining edge is the first edge of `p`'s suffix; the rest lie in the interior. -/
private lemma edges_pathOfTwoPaths_subset [DecidableEq α] {p q : SimplePath α}
    (d : DivergenceData p q) {e : Sym2 α} (he : e ∈ (pathOfTwoPaths d).edges) :
    e ∈ p.edges ∨ e ∈ q.edges := by
  have hpPos := d.length_left
  have hpHead := d.head_left
  have heS' : e = s(d.vertex, (erasedInterior d).head) ∨ e ∈ (erasedInterior d).edges := by
    simpa [pathOfTwoPaths, SimplePath.edges_append] using he
  rcases heS' with heJoin | heT
  · subst e
    refine Or.inl (SimplePath.edges_suffixFrom_subset p d.vertex d.mem_left ?_)
    have hfirst := VertexSeq.first_edge_mem (p.suffixFrom d.vertex d.mem_left).vertices hpPos
    simpa [hpHead, head_erasedInterior d] using hfirst
  · exact edges_erasedInterior_subset d heT

/-- Two distinct simple paths with the same endpoints determine a simple cycle
by loop-erasing the interior of the closed walk formed after their first
divergence, then restoring the two incident edges at that divergence. -/
def ofTwoPaths [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) : SimpleCycle α :=
  ofPathClosing (pathOfTwoPaths (divergenceData p q hhead htail hne))
    (two_le_length_pathOfTwoPaths (divergenceData p q hhead htail hne))

/-- The cycle selected from two distinct paths is no longer than the two paths
combined. -/
lemma length_ofTwoPaths [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    (ofTwoPaths p q hhead htail hne).length ≤ p.length + q.length := by
  set d := divergenceData p q hhead htail hne with hd
  have hclose : (ofTwoPaths p q hhead htail hne).length = (pathOfTwoPaths d).length + 1 := by
    unfold ofTwoPaths; rw [length_ofPathClosing]
  have hpath := length_pathOfTwoPaths d
  have herase := length_erasedInterior_le d
  have hint := length_interiorWalk d
  have hple : (p.suffixFrom d.vertex d.mem_left).length ≤ p.length :=
    VertexSeq.length_suffixFrom_le p.vertices d.vertex d.mem_left
  have hqle : (q.suffixFrom d.vertex d.mem_right).length ≤ q.length :=
    VertexSeq.length_suffixFrom_le q.vertices d.vertex d.mem_right
  omega

/-- The selected cycle is rooted at a vertex of the first path. -/
lemma head_ofTwoPaths_mem_left [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    (ofTwoPaths p q hhead htail hne).head ∈ p.vertices := by
  have hh : (ofTwoPaths p q hhead htail hne).head =
      (divergenceData p q hhead htail hne).vertex := by
    unfold ofTwoPaths; rw [head_ofPathClosing, head_pathOfTwoPaths]
  rw [hh]
  exact (divergenceData p q hhead htail hne).mem_left

/-- Every edge of the selected cycle comes from one of the two input paths. -/
lemma edges_ofTwoPaths_subset [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) {e : Sym2 α}
    (he : e ∈ (ofTwoPaths p q hhead htail hne).edges) :
    e ∈ p.edges ∨ e ∈ q.edges := by
  unfold ofTwoPaths at he
  set d := divergenceData p q hhead htail hne with hd
  rw [edges_ofPathClosing, List.mem_append, List.mem_singleton] at he
  rcases he with hpath | hclose
  · exact edges_pathOfTwoPaths_subset d hpath
  · subst e
    refine Or.inr (SimplePath.edges_suffixFrom_subset q d.vertex d.mem_right ?_)
    have hkey : s((pathOfTwoPaths d).tail, (pathOfTwoPaths d).head) ∈
        (q.suffixFrom d.vertex d.mem_right).edges := by
      have hH : (pathOfTwoPaths d).head = d.vertex := head_pathOfTwoPaths d
      have hT : (pathOfTwoPaths d).tail =
          (q.suffixFrom d.vertex d.mem_right).vertices.dropHead.head := by
        rw [tail_pathOfTwoPaths]; exact tail_erasedInterior d
      simpa [hH, hT, d.head_right, Sym2.eq_swap] using
        VertexSeq.first_edge_mem (q.suffixFrom d.vertex d.mem_right).vertices d.length_right
    exact hkey

/-! ## reverse -/

/-- Reverse the orientation of a simple cycle. -/
@[grind] def reverse (c : SimpleCycle α) : SimpleCycle α :=
  ⟨c.val.reverse, SimpleWalk.IsCycle.reverse c.val c.2⟩

/-! ## reroot -/

/-- The suffix rooted at a cycle vertex can be glued to the preceding prefix. -/
private lemma tail_suffixFrom_eq_head_prefixUntil [DecidableEq α] (c : SimpleCycle α)
    (u : α) (hu : u ∈ vertices c) :
    (c.val.suffixFrom u hu).val.tail = (c.val.prefixUntil u hu).val.head := by
  simpa using (closed c).symm

/-- Re-rooting the underlying walk of a simple cycle at a non-head vertex
preserves the cycle property. -/
private lemma isCycle_reroot_glue [DecidableEq α] (c : SimpleCycle α) (u : α)
    (hu : u ∈ vertices c) (hhead : u ≠ head c) :
    SimpleWalk.IsCycle
      ((c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu)
        (tail_suffixFrom_eq_head_prefixUntil c u hu)) := by
  let pre : VertexSeq α := (vertices c).prefixUntil u hu
  let suf : VertexSeq α := (vertices c).suffixFrom u hu
  have hpre_pos : pre.length ≠ 0 := fun hz =>
    hhead (by simpa [pre] using (VertexSeq.head_eq_tail_of_length_zero pre hz).symm)
  have hsuf_pos : suf.length ≠ 0 := fun hz => hhead
    ((show u = (vertices c).tail by
      simpa [suf] using VertexSeq.head_eq_tail_of_length_zero suf hz).trans (closed c).symm)
  have hsplit' : pre.dropTail.append suf = vertices c := by
    simpa [pre, suf] using
      VertexSeq.dropTail_prefixUntil_append_suffixFrom (vertices c) u hu hhead
  have hleft : (pre.dropTail.append suf.dropTail).nodup := by
    rw [← VertexSeq.dropTail_append pre.dropTail suf hsuf_pos,
      congrArg VertexSeq.dropTail hsplit']
    exact c.2.2.2
  have hsuf_pos' : ((c.val.suffixFrom u hu).val.length ≠ 0) := by simpa [suf] using hsuf_pos
  have hlenAll : pre.dropTail.length + suf.length + 1 = (vertices c).length := by
    simpa [VertexSeq.length_append] using congrArg VertexSeq.length hsplit'
  have hpreLen := VertexSeq.length_dropTail_succ pre hpre_pos
  have hsufLen := VertexSeq.length_dropTail_succ suf hsuf_pos
  have h3 : 3 ≤ (vertices c).length := c.2.1
  simp only [SimpleWalk.IsCycle, SimpleWalk.glue, hsuf_pos']
  refine ⟨?_, ?_, ?_⟩
  · change 3 ≤ (suf.dropTail.append pre).length
    rw [VertexSeq.length_append]
    omega
  · change (suf.dropTail.append pre).closed
    simp [VertexSeq.closed, pre, suf]
  · change (suf.dropTail.append pre).dropTail.nodup
    rw [VertexSeq.dropTail_append suf.dropTail pre hpre_pos]
    exact VertexSeq.nodup_append_comm pre.dropTail suf.dropTail hleft

/-- Re-root a simple cycle at any vertex on it. -/
def reroot [DecidableEq α] (c : SimpleCycle α) (u : α) (hu : u ∈ vertices c) :
    SimpleCycle α :=
  if hhead : u = head c then
    c
  else
    ⟨(c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu)
        (tail_suffixFrom_eq_head_prefixUntil c u hu),
      isCycle_reroot_glue c u hu hhead⟩

/-! ## edges -/

/-- The number of traversed edges equals the cycle's length. -/
@[simp] lemma length_edges (c : SimpleCycle α) : (edges c).length = length c :=
  VertexSeq.length_edges (vertices c)

/-- A simple cycle has at least three traversed edges. -/
lemma three_le_length_edges (c : SimpleCycle α) : 3 ≤ (edges c).length := by
  rw [length_edges]
  exact c.2.1

/-- A simple cycle traverses at least one edge. -/
lemma edges_ne_nil (c : SimpleCycle α) : edges c ≠ [] := by
  grind [three_le_length_edges]

/-- The edge list is the interior path's edge list plus the closing edge. -/
lemma edges_eq_interior_concat (c : SimpleCycle α) :
    edges c = SimplePath.edges (interior c) ++ [s(SimplePath.tail (interior c), tail c)] := by
  have hpos : (vertices c).length ≠ 0 := by grind
  simpa [List.concat_eq_append] using VertexSeq.edges_eq_dropTail_concat (vertices c) hpos

/-- A simple cycle traverses each edge at most once. -/
lemma edges_nodup (c : SimpleCycle α) : (edges c).Nodup := by
  rw [edges_eq_interior_concat, List.nodup_append]
  refine ⟨SimplePath.edges_nodup (interior c), by simp, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst hb; subst hab
  have hclosedTail : tail c = SimplePath.head (interior c) := by
    grind [VertexSeq.head_dropTail, closed]
  rw [hclosedTail] at ha
  have hle := VertexSeq.length_le_one_of_closing_edge_mem_swap
    (SimplePath.vertices (interior c)) (SimplePath.nodup (interior c)) ha
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hdrop := VertexSeq.length_dropTail_succ (vertices c) (by omega)
  change (vertices c).dropTail.length ≤ 1 at hle
  omega

/-- Reversal reverses the edge list. -/
@[simp] lemma edges_reverse (c : SimpleCycle α) :
    edges (reverse c) = (edges c).reverse :=
  VertexSeq.edges_reverse (vertices c)

/-! ## arcs -/

/-- The number of traversed arcs equals the cycle's length. -/
@[simp] lemma length_arcs (c : SimpleCycle α) : (arcs c).length = length c :=
  VertexSeq.length_arcs (vertices c)

/-- A simple cycle has at least three traversed arcs. -/
lemma three_le_length_arcs (c : SimpleCycle α) : 3 ≤ (arcs c).length := by
  rw [length_arcs]
  exact c.2.1

/-- A simple cycle traverses at least one arc. -/
lemma arcs_ne_nil (c : SimpleCycle α) : arcs c ≠ [] := by
  grind [three_le_length_arcs]

/-- The arc list is the interior path's arc list plus the closing arc. -/
lemma arcs_eq_interior_concat (c : SimpleCycle α) :
    arcs c =
      SimplePath.arcs (interior c) ++ [(SimplePath.tail (interior c), tail c)] := by
  have hpos : (vertices c).length ≠ 0 := by grind
  simpa [List.concat_eq_append] using VertexSeq.arcs_eq_dropTail_concat (vertices c) hpos

/-- A simple cycle traverses each directed arc at most once. -/
lemma arcs_nodup (c : SimpleCycle α) : (arcs c).Nodup := by
  rw [arcs_eq_interior_concat, List.nodup_append]
  refine ⟨SimplePath.arcs_nodup (interior c), by simp, ?_⟩
  have hclosedTail : tail c = SimplePath.head (interior c) := by
    grind [VertexSeq.head_dropTail, closed]
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hdrop := VertexSeq.length_dropTail_succ (vertices c) (by omega)
  grind [VertexSeq.length_le_one_of_closing_arc_mem]

/-- Reversal reverses the arc list and swaps every arc's endpoints. -/
@[simp] lemma arcs_reverse (c : SimpleCycle α) :
    arcs (reverse c) = (arcs c).reverse.map (fun a : α × α => (a.2, a.1)) :=
  VertexSeq.arcs_reverse (vertices c)

end SimpleCycle
