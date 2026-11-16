# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""Transformer parameter lattices: exact counts, bits, symmetry orders, Occam radius.

Chapter 18 (Learning Machines).  Exact integer arithmetic for the counts;
log2 of factorials via math.lgamma (floating point, used only for display).
"""
import math


def gpt2_params(V, T, d, L):
    # per block: LN1 2d, QKV 3d^2+3d, proj d^2+d, LN2 2d, MLP 4d^2+4d and 4d^2+d
    block = 2 * d + (3 * d * d + 3 * d) + (d * d + d) + 2 * d + (4 * d * d + 4 * d) + (4 * d * d + d)
    assert block == 12 * d * d + 13 * d
    return V * d + T * d + L * block + 2 * d          # tied unembedding, final LN


def llama_params(V, d, f, L):
    block = 2 * d + 4 * d * d + 3 * d * f              # RMSNorm gains, W_QKVO, SwiGLU
    return 2 * V * d + L * block + d                   # untied embedding/unembedding


def log2_fact(n):
    return math.lgamma(n + 1) / math.log(2)


N_gpt2 = gpt2_params(50257, 1024, 768, 12)
N_llama = llama_params(32000, 4096, 11008, 32)
assert N_gpt2 == 124_439_808
assert N_llama == 6_738_415_616
print("GPT-2 small parameters:", N_gpt2)
print("LLaMA-7B parameters:  ", N_llama)

# distinct finite values per parameter
bf16_values = 2 ** 16 - 2 * 2 ** 7 - 1     # minus inf/NaN patterns, minus the duplicate -0
assert bf16_values == 65279
formats = {"fp32": 32, "bf16": 16, "int8": 8, "int4": 4}

# discrete lattice-preserving symmetry group, log2 of the order
def log2_group_gpt2(d=768, L=12, H=12):
    dh = d // H
    head_gauge = 2 * (dh + log2_fact(dh))        # signed perms for QK and for VO
    block = log2_fact(H) + H * head_gauge + log2_fact(4 * d)
    return log2_fact(d) + L * block              # residual permutations (LayerNorm)


def log2_group_llama(d=4096, L=32, H=32, f=11008):
    dh = d // H
    qk = dh                                      # RoPE: units {+-1, +-i} per plane: 4^(dh/2)
    vo = dh + log2_fact(dh)
    block = log2_fact(H) + H * (qk + vo) + f + log2_fact(f)   # SwiGLU: signed perms
    return d + log2_fact(d) + L * block          # residual signed perms (RMSNorm)


G2, GL = log2_group_gpt2(), log2_group_llama()
print("log2 |G| GPT-2 small: %.4g   (fraction of the bf16 bits: %.2e)" % (G2, G2 / (16 * N_gpt2)))
print("log2 |G| LLaMA-7B:    %.4g   (fraction of the bf16 bits: %.2e)" % (GL, GL / (16 * N_llama)))
assert G2 / (16 * N_gpt2) < 1e-3 and GL / (16 * N_llama) < 1e-3


def occam_radius(N, bits, m, delta=0.01):
    """t with (#lattice) exp(-m t^2) = delta, #lattice = 2^(N bits)."""
    return math.sqrt((N * bits * math.log(2) + math.log(1 / delta)) / m)


def m_needed(N, bits, t, delta=0.01):
    return (N * bits * math.log(2) + math.log(1 / delta)) / t ** 2


print("\nlattice bits and Occam sample sizes for radius t = 0.1, delta = 0.01")
for name, N in (("GPT-2 small", N_gpt2), ("LLaMA-7B", N_llama)):
    for fmt, b in formats.items():
        print("  %-11s %-4s  log2|Lambda| = %.3e   m(t=0.1) = %.2e" % (name, fmt, N * b, m_needed(N, b, 0.1)))

t_tok = occam_radius(N_llama, 16, 1.0e12)
t_seq = occam_radius(N_llama, 16, 1.0e12 / 2048)
print("\nLLaMA-7B bf16, m = 1e12 i.i.d. examples: t = %.3f" % t_tok)
print("LLaMA-7B bf16, m = 1e12/2048 sequences:  t = %.1f (vacuous: t > 1/2)" % t_seq)
assert 0.27 < t_tok < 0.28 and t_seq > 0.5
print("all assertions passed")
