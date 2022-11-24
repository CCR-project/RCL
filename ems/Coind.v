From Coinduction Require Import coinduction.


(***
simg로 증명 가능했다면 _simg_safe simg로 증명 가능하다?
***)

(***
b: X -> X (monotone. i.e., order preserving)

vb = U { r | r <= b r }

bvb = vb

∀ x <= bx. bx ∈ vb, ∵ b(x) <= b(bx) (∵ monotonoe)


enhancement (cawu)

∃ y. x <= y <= bfy
------------------------------
x <= vb



tarski (paco)

x <= bx
------------------------------
x <= vb



tarski (paco)
x <= vb <-> ∃ r. x <= r <= br



strong coinduction (paco)

x <= vb <-> x <= b(x u vb)



tarski (cawu)

∃ y. x <= y <= by
------------------------------
x <= vb



sound up-to (paco)

x <= bfx      f is monotone
------------------------------
x <= vb



sound down-to?

x <= vb
------------------------------
x <= bfx



***)
