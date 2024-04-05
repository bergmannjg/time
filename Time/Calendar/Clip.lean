import Time.Interval
import Time.Fixed

namespace Time

namespace Clip

def clipToNonemptyIcc (a b : Nat) (x : Int) (h : a <= b) : NonemptyIcc a b :=
  let x'' := x.toNat
  let icc : Time.Icc a b :=
    if ha : x'' < a then ⟨a, And.intro (by simp) h⟩
    else if hb : x'' > b then ⟨b, And.intro h (by simp)⟩
    else
      ⟨x'', And.intro (Nat.not_lt.1 ha) (Nat.not_lt.1 hb) ⟩

  toNonemptyIcc icc h

def clip (a b : Nat) (x : Int) (h : a <= b) : Nat :=
  (clipToNonemptyIcc a b x h).icc.val

def clipToNonemptyIcc? (a b : Nat) (x : Int) (h : a <= b) : Option $ NonemptyIcc a b :=
  let x'' := x.toNat
  let icc : Option $ Time.Icc a b :=
    if ha : x'' < a then none
    else if hb : x'' > b then none
    else
      some ⟨x'', And.intro (Nat.not_lt.1 ha) (Nat.not_lt.1 hb) ⟩

  icc |> Option.map (λ icc => toNonemptyIcc icc h)

def clipToNonemptyIco? (a b : Nat) (x : Int) (h : a < b) : Option $ NonemptyIco a b :=
  let x'' := x.toNat
  let ico : Option $ Time.Ico a b :=
    if ha : x'' < a then none
    else if hb : x'' >= b then none
    else
      some ⟨x'', And.intro (Nat.not_lt.1 ha) (Nat.not_le.1 hb) ⟩

  ico |> Option.map (λ ico => toNonemptyIco ico h)

def clip? (a b : Nat) (x : Int) (h : a <= b) : Option Nat :=
  clipToNonemptyIcc? a b x h |> Option.map (λ v => v.icc.val)

def clipToIco? (a : Fixed p) (b : Fixed p) (x : Fixed p) : Option $ Time.Ico a b :=
  if ha : a.val ≤ x.val then
    if hb : x.val < b.val then some ⟨x, And.intro ha hb⟩
    else none
  else none
