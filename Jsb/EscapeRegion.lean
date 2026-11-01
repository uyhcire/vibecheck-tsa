import Jsb.Conformance
import Jsb.KernelRfl

/-! One-tick escape properties over boxes around a pulled-up climb state (35-45 m/s, flight path -0.1..0.05,
alpha 0.10..0.16 in the full region of `Tools/BoxProbe.lean`), proved by kernel evaluation of `checkRec`. -/

namespace Jsb
open Vibecheck

def CLOf.ofList (l : List Iv) : CLOf Iv :=
  let f (i : Nat) : Iv := l.getD i .top
  ⟨⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩, f 19⟩

namespace EscapeRegion

/-- 0.03125 m/s per tick: vertical acceleration at least 0.5 m/s^2 over the tick (raw) -/
def dvzMin : Int := 2048
/-- -0.1 m/s per tick: horizontal deceleration at most 1.6 m/s^2 (raw) -/
def dvxMin : Int := -6554

/-- Flight path in [-0.1, 0.05] (as vz/vx), alpha proxy dz - vz/40 in [0.10, 0.16], and consistency of the
derivative and history fields (|au - au1| ≤ 0.13, |ah - ah1| ≤ 0.04, |vz - pvz|, |pvz - pvz2| ≤ 0.11). -/
def cons : List LinCon :=
  [⟨[(10, 3), (1, 2)], 0, 65536000⟩, ⟨[(1, 2), (-20, 3)], 0, 65536000⟩, ⟨[(40, 5), (-1, 3)], 262144, 419430⟩,
   ⟨[(1, 13), (-1, 16)], -8520, 8520⟩, ⟨[(1, 12), (-1, 15)], -2621, 2621⟩, ⟨[(1, 3), (-1, 17)], -7209, 7209⟩,
   ⟨[(1, 17), (-1, 18)], -7209, 7209⟩]

def dims : List (Nat × Int) := [(1, 32), (2, 40700), (3, 53900), (4, 525000), (5, 2690000), (6, 121000), (7, 23),
  (8, 10), (12, 2070), (13, 2380), (15, 610), (16, 620), (19, 70900)]

/-- 5% of the full region in every coordinate. -/
def box5 : CLOf Iv := CLOf.ofList [.box (0) (0), .box (59555840) (61685760), .box (2605056) (2637824), .box (-67584) (-47104), .box (64870) (64931), .box (6947) (7471), .box (7569) (8159), .box (140804096) (144932864), .box (4931584) (5029888), .box (655) (12452), .box (-217088) (-195789), .box (0) (0), .box (-17203) (-2458), .box (455311) (494961), .box (4309) (6832), .box (-17203) (-2458), .box (454984) (495288), .box (-72581) (-51937), .box (-76022) (-55050), .box (13045) (13956)]

/-- 10% of the full region in every coordinate. -/
def box10 : CLOf Iv := CLOf.ofList [.box (0) (0), .box (58490880) (62750720), .box (2588672) (2654208), .box (-77824) (-36864), .box (64839) (64961), .box (6685) (7733), .box (7274) (8454), .box (138739712) (146997248), .box (4882432) (5079040), .box (-5243) (18350), .box (-227738) (-185139), .box (0) (0), .box (-24576) (4915), .box (435487) (514785), .box (3047) (8094), .box (-24576) (4915), .box (434831) (515441), .box (-82903) (-41615), .box (-86508) (-44564), .box (12589) (14411)]

theorem escape_box5 : ∀ c, box5.Mem c → (∀ l ∈ cons, l.Holds c) → IncrProp dvzMin dvxMin c :=
  region_sound dvzMin dvxMin cons dims 8 box5 (by decide +kernel)

/-- Sub-box reached from `B` by a path of bisection choices (`true` = upper half). -/
def sub (B : CLOf Iv) (p : List Bool) : CLOf Iv :=
  p.foldl (fun B b => if b then (halve B (pick dims B)).2 else (halve B (pick dims B)).1) B

def Q (c : CLOf Fx) : Prop := (∀ l ∈ cons, l.Holds c) → IncrProp dvzMin dvxMin c

theorem sub_cover (B : CLOf Iv) (p : List Bool) (h0 : ∀ c, (sub B (p ++ [false])).Mem c → Q c)
    (h1 : ∀ c, (sub B (p ++ [true])).Mem c → Q c) : ∀ c, (sub B p).Mem c → Q c := by
  intro c hc
  simp only [sub, List.foldl_append, List.foldl_cons, List.foldl_nil, ite_true, ite_false, Bool.false_eq_true] at h0 h1
  rcases halve_cover hc (pick dims (sub B p)) with h | h
  · exact h0 c h
  · exact h1 c h

theorem sub_sound (B : CLOf Iv) (p : List Bool) (n : Nat)
    (h : checkRec (incrOK dvzMin dvxMin) cons dims n (sub B p) = true) : ∀ c, (sub B p).Mem c → Q c :=
  fun c hm hl => region_sound dvzMin dvxMin cons dims n (sub B p) h c hm hl

-- kernel evaluation of ~20-40 interval ticks exceeds the default budget
set_option maxHeartbeats 20000000 in
theorem box10_ff : ∀ c, (sub box10 [false, false]).Mem c → Q c := sub_sound _ _ 12 (by decide +kernel)
-- kernel evaluation of ~20-40 interval ticks exceeds the default budget
set_option maxHeartbeats 20000000 in
theorem box10_ft : ∀ c, (sub box10 [false, true]).Mem c → Q c := sub_sound _ _ 12 (by decide +kernel)
-- kernel evaluation of ~20-40 interval ticks exceeds the default budget
set_option maxHeartbeats 20000000 in
theorem box10_tf : ∀ c, (sub box10 [true, false]).Mem c → Q c := sub_sound _ _ 12 (by decide +kernel)
-- kernel evaluation of ~20-40 interval ticks exceeds the default budget
set_option maxHeartbeats 20000000 in
theorem box10_tt : ∀ c, (sub box10 [true, true]).Mem c → Q c := sub_sound _ _ 12 (by decide +kernel)

theorem escape_box10 : ∀ c, box10.Mem c → (∀ l ∈ cons, l.Holds c) → IncrProp dvzMin dvxMin c :=
  sub_cover box10 [] (sub_cover box10 [false] box10_ff box10_ft) (sub_cover box10 [true] box10_tf box10_tt)

end EscapeRegion
end Jsb

