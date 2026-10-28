"""Blind simultaneous release: window, feasibility ceiling and pad length for Ethereum timings.

Feasibility (Theorem 5 with Theorem 2(a)): gamma_max = Theta / omega with Theta = W - omega, where
W = t2 - t1 is the host design's window between fixing the set of ciphertexts and the time by which
release values must be public.

Instantiation on the ticket-first threshold design (Herold, ethresear.ch 26040):
  * t1: B[n+1] (which records etx_seen) is fast-confirmed, a few seconds into its slot;
  * t2: start of slot n+2, whose beacon block must carry the key (under ePBS the builder commits to
    its payload hash in the bid, so values are needed at the slot start).
  So W = slot - t_fc. Escrowing on receipt of B[n+1] gives W = slot (no reorg refusal).
Six-second slots scale the fast-confirmation point proportionally (an assumption, not a measurement).

Pad length L = Theta * nu_h with nu_h = 1 / (70 ns), the measured SHA-256 step on a 2.1 GHz Xeon.
Also: the sender-side time-lock ceiling in the same design, 1 + Delta/delta with delta ~ Delta ~ slot.
"""
import json

NS_PER_STEP = 70e-9
NU_H = 1 / NS_PER_STEP


def gmax(W, omega):
    return (W - omega) / omega


def pad_length(theta):
    return theta * NU_H


def rows():
    out = []
    cases = [
        # (slot, label, W)
        (12, "fast-confirmed B[n+1], t_fc = 4 s", 12 - 4),
        (12, "fast-confirmed B[n+1], t_fc = 3 s", 12 - 3),
        (12, "escrow on receipt of B[n+1]", 12),
        (6, "fast-confirmed B[n+1], t_fc = 2 s", 6 - 2),
        (6, "fast-confirmed B[n+1], t_fc = 1.5 s", 6 - 1.5),
    ]
    for slot, label, W in cases:
        for omega in (2.0, 1.0):
            theta = W - omega
            out.append({
                "slot_s": slot, "case": label, "W_s": W, "omega_s": omega,
                "Theta_s": theta, "gamma_max": round(gmax(W, omega), 3),
                "pad_length": round(pad_length(theta)),
            })
    return out


def sender_timelock_ceiling(slot=12, t_pub_in_slot=0.5):
    """Ticket-first design: etx published in slot n, must stay private until slot n+1's payload is
    fixed (start of n+1), and must be open by the start of n+2. Honest solvers start at broadcast."""
    t_pub = t_pub_in_slot
    t1 = slot
    t2 = 2 * slot
    return (t2 - t_pub) / (t1 - t_pub)


if __name__ == "__main__":
    table = rows()
    print(f"{'slot':>4} {'W':>5} {'omega':>5} {'Theta':>5} {'gamma_max':>9} {'pad L':>12}  case")
    for r in table:
        print(f"{r['slot_s']:>4} {r['W_s']:>5} {r['omega_s']:>5} {r['Theta_s']:>5} "
              f"{r['gamma_max']:>9} {r['pad_length']:>12.3e}  {r['case']}")
    s = sender_timelock_ceiling()
    print(f"\nsender-side time-lock ceiling in the ticket-first design (12 s slots): {s:.2f}")
    with open("bsr_params.json", "w") as f:
        json.dump({"rows": table, "sender_timelock_ceiling_12s": s}, f, indent=2)
