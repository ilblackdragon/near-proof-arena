import ZkFormal.NearV3.Render.Ups.TreeMetadata

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

def FixedSuffix (key : List Nat) : Prop := key=[] ∨ key=[15] ∨ key=[0,15]

theorem FixedSuffix.length {key : List Nat} (h : FixedSuffix key) : key.length≤2 := by
  rcases h with rfl|rfl|rfl <;> decide

theorem FixedSuffix.canonical {key : List Nat} (h : FixedSuffix key) :
    key=[0,15].drop (2-key.length) := by rcases h with rfl|rfl|rfl <;> rfl

theorem FixedSuffix.cursor {key : List Nat} (h : FixedSuffix key) {n : Nat} (hn : n≤key.length) :
    1≤2-key.length+n+1 ∧ 2-key.length+n+1≤3 := by have hh := h.length; omega

theorem FixedSuffix.fresh {key : List Nat} (h : FixedSuffix key) (n : Nat) :
    key.drop (n+1)=[0,15].drop (2-key.length+n+1) := by
  conv => lhs; rw [h.canonical]
  rw [List.drop_drop]
  congr 1

theorem FixedSuffix.prefix {key : List Nat} (h : FixedSuffix key) (n : Nat) :
    key.take n=([0,15].drop ((2-key.length+n+1)-1-n)).take n := by
  rw [show 2-key.length+n+1-1-n=2-key.length by omega]
  exact congrArg (List.take n) h.canonical

theorem FixedSuffix.next {key : List Nat} (h : FixedSuffix key) {n y : Nat} {ys : List Nat}
    (hd : key.drop n=y::ys) : y=if 2-key.length+n+1=1 then 0 else 15 := by
  have hl := congrArg List.length hd
  simp only [List.length_drop,List.length_cons] at hl
  rcases h with rfl|rfl|rfl
  · simp at hl
  · have hn : n=0 := by simp at hl; omega
    subst n
    simp at hd
    exact hd.1.symm
  · have hn : n=0 ∨ n=1 := by simp at hl; omega
    rcases hn with rfl|rfl <;> simp at hd ⊢ <;> exact hd.1.symm

theorem FixedSuffix.wrap {key : List Nat} (h : FixedSuffix key) {n : Nat}
    (hn : n≤key.length) (hp : 0<n) :
    (2-key.length+n+1=2 ∧ n=1) ∨ (2-key.length+n+1=3 ∧ n=1) ∨
    (2-key.length+n+1=3 ∧ n=2) := by have hh := h.length; omega
end ZkFormal.NearV3.Render.UpsGen
