"""
Exact rational win-probability DP for Elevens-style solitaire.

Uses rank-multiset state (suits are irrelevant — proved in Lean). The state is
(board, pile) where each is a tuple of counts indexed by rank (0-based).

Supports two configurations via GameParams:
  - Full 13-rank game (FULL_PARAMS / FULL_FLIP_PARAMS): 52 cards, board size 9,
    pairs summing to 11, J/Q/K triples. Computes the exact win probabilities
    proved in the paper (~175s, 462,983 canonical states).
  - POC 6-rank game (POC_PARAMS): 12 cards, board size 4, pairs summing to 7.
    Used for Lean DP verification (poc_win_prob = 3217/5775).
"""

from __future__ import annotations

import math
import random as _random
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class GameParams:
    """
    Parameters defining an Elevens-style solitaire variant.

    Attributes:
        n_ranks: Number of distinct ranks (e.g., 6 for the POC, 13 for full game).
        copies_per_rank: Number of copies of each rank in the deck.
        board_size: Number of board slots.
        complement_pairs: Pairs of rank indices (0-based) that form a legal pair move.
        triple_groups: Tuples of rank indices that form a legal triple move (e.g., JQK).
        flip: If True, when stuck with a non-empty pile, flip the top card. If it
              pairs (sum to 11) with a board card, remove both and refill one slot;
              otherwise lose. Flip only enables pairs, never triples.
    """
    n_ranks: int
    copies_per_rank: int
    board_size: int
    complement_pairs: tuple[tuple[int, int], ...]
    triple_groups: tuple[tuple[int, int, int], ...]
    flip: bool = False


# POC: ranks 1-6, pairs summing to 7, board 4, 2 copies each.
# Rank indices: 0=rank1, 1=rank2, ..., 5=rank6
# Complement pairs: (0,5)=1+6, (1,4)=2+5, (2,3)=3+4
SCALED_PARAMS = GameParams(
    n_ranks=6,
    copies_per_rank=2,
    board_size=4,
    complement_pairs=((0, 5), (1, 4), (2, 3)),
    triple_groups=(),
)

SCALED_FLIP_PARAMS = GameParams(
    n_ranks=6,
    copies_per_rank=2,
    board_size=4,
    complement_pairs=((0, 5), (1, 4), (2, 3)),
    triple_groups=(),
    flip=True,
)

# Full Elevens: 13 ranks, 4 copies, board 9.
# Rank indices: 0=A,1=2,...,9=10,10=J,11=Q,12=K
# Complement pairs: (A,10)=(0,9),(2,9)=(1,8),(3,8)=(2,7),(4,7)=(3,6),(5,6)=(4,5)
FULL_PARAMS = GameParams(
    n_ranks=13,
    copies_per_rank=4,
    board_size=9,
    complement_pairs=((0, 9), (1, 8), (2, 7), (3, 6), (4, 5)),
    triple_groups=((10, 11, 12),),
)

FULL_FLIP_PARAMS = GameParams(
    n_ranks=13,
    copies_per_rank=4,
    board_size=9,
    complement_pairs=((0, 9), (1, 8), (2, 7), (3, 6), (4, 5)),
    triple_groups=((10, 11, 12),),
    flip=True,
)


def _make_win_prob(params: GameParams):
    """
    Build and return a memoized win_prob function for the given GameParams.

    Returns win_prob(board, pile) -> Fraction.

    Caches on a symmetry-canonical key, exploiting two game automorphisms:
    1. Complement pairs are interchangeable: (A,10), (2,9), ... all have the
       same structure, so permuting which pair is "first" doesn't change P(win).
    2. Within each complement pair, the two ranks are interchangeable (since
       a+b = 11 = b+a). Same for face ranks in a triple (J/Q/K each appear once).

    Symmetry group size: n_pairs! × 2^n_pairs × n_face! (up to 23,040 for full game).
    This typically reduces the effective state count by 100-1000×.
    """
    n_ranks = params.n_ranks
    pairs = params.complement_pairs
    triples = params.triple_groups
    use_flip = params.flip

    # Identify which ranks are in complement pairs vs. triples (face ranks)
    pair_rank_set = set(r for pair in pairs for r in pair)
    # Face ranks: all ranks appearing in any triple, not in any pair
    face_rank_set = set(r for triple in triples for r in triple) - pair_rank_set
    face_ranks = sorted(face_rank_set)

    # Map each numeric rank to its complement (for flip logic)
    rank_to_complement: dict[int, int] = {}
    for (a, b) in pairs:
        rank_to_complement[a] = b
        rank_to_complement[b] = a

    def _canonicalize(board: tuple, pile: tuple) -> tuple:
        """
        Compute a canonical representative of (board, pile) under the symmetry group.

        Key structure:
          - pair_sigs: for each complement pair, record (board, pile) counts for
            both ranks, sort within the pair (ranks interchangeable), then sort
            across pairs (pairs interchangeable).
          - face_sigs: for each face rank, record (board, pile) counts, sorted
            across face ranks (interchangeable in triples).
        """
        # Within each pair, sort (rank_a_info, rank_b_info) so lower comes first
        pair_sigs = sorted(
            tuple(sorted([(board[a], pile[a]), (board[b], pile[b])]))
            for (a, b) in pairs
        )
        # Sort face ranks too (J/Q/K interchangeable in JQK triple)
        face_sigs = tuple(sorted((board[r], pile[r]) for r in face_ranks))
        return (tuple(pair_sigs), face_sigs)

    def _find_legal_move(board: tuple) -> tuple | None:
        """Return the first legal move found, or None if stuck."""
        for (a, b) in pairs:
            if board[a] > 0 and board[b] > 0:
                return (a, b)
        for triple in triples:
            if all(board[r] > 0 for r in triple):
                return triple
        return None

    # Use an explicit dict so we can report cache size separately from lru_cache
    _cache: dict = {}

    def win_prob(board: tuple, pile: tuple) -> Fraction:
        """
        Exact P(win) from the given board+pile state.

        Both board and pile are tuples of rank counts (length = n_ranks).
        Uses the first legal move found (safe by confluence — outcome is
        move-order independent).
        """
        key = _canonicalize(board, pile)
        if key in _cache:
            return _cache[key]

        board_total = sum(board)
        pile_total = sum(pile)

        # Win condition: board and pile both exhausted
        if board_total == 0 and pile_total == 0:
            _cache[key] = Fraction(1)
            return Fraction(1)

        move = _find_legal_move(board)
        if move is None:
            if not use_flip or pile_total == 0:
                # No regular moves, no flip available → loss
                _cache[key] = Fraction(0)
                return Fraction(0)

            # Flip: draw top card from pile (random among remaining ranks),
            # weighted by each rank's pile count / pile_total.
            # Flip only succeeds if the drawn card is numeric and its complement
            # is present on the board. On success, remove both and refill one slot.
            prob = Fraction(0)
            for r in range(n_ranks):
                if pile[r] == 0:
                    continue
                flip_weight = Fraction(pile[r], pile_total)
                comp = rank_to_complement.get(r)
                if comp is None or board[comp] == 0:
                    # Face card or no board match → this flip outcome is a loss
                    continue

                # Flip succeeds: remove flip card (rank r) from pile,
                # remove board card (rank comp), then refill one slot.
                post_flip_pile = list(pile)
                post_flip_pile[r] -= 1
                post_flip_board = list(board)
                post_flip_board[comp] -= 1
                new_pile_total = pile_total - 1

                if new_pile_total == 0:
                    prob += flip_weight * win_prob(
                        tuple(post_flip_board), tuple(post_flip_pile)
                    )
                else:
                    # Draw 1 card to refill the vacated slot, weighted by rank probability
                    for rr in range(n_ranks):
                        if post_flip_pile[rr] == 0:
                            continue
                        refill_weight = Fraction(post_flip_pile[rr], new_pile_total)
                        next_pile = list(post_flip_pile)
                        next_pile[rr] -= 1
                        next_board = list(post_flip_board)
                        next_board[rr] += 1
                        prob += flip_weight * refill_weight * win_prob(
                            tuple(next_board), tuple(next_pile)
                        )

            _cache[key] = prob
            return prob

        # Apply move: decrement removed ranks
        new_board = list(board)
        for r in move:
            new_board[r] -= 1
        k = len(move)
        k_draw = min(k, pile_total)

        if k_draw == 0:
            result = win_prob(tuple(new_board), pile)
            _cache[key] = result
            return result

        # Enumerate all multisets of size k_draw drawable from pile,
        # weighted by multivariate hypergeometric probability.
        denom = math.comb(pile_total, k_draw)
        prob = Fraction(0)

        for draw in _enumerate_draws(pile, k_draw):
            weight_num = 1
            for r in range(n_ranks):
                weight_num *= math.comb(pile[r], draw[r])
            if weight_num == 0:
                continue
            new_pile = tuple(pile[r] - draw[r] for r in range(n_ranks))
            next_board = tuple(new_board[r] + draw[r] for r in range(n_ranks))
            prob += Fraction(weight_num, denom) * win_prob(next_board, new_pile)

        _cache[key] = prob
        return prob

    # Attach cache for external inspection
    win_prob._cache = _cache  # type: ignore[attr-defined]

    def cache_info():
        n = len(_cache)
        return type("CacheInfo", (), {"currsize": n, "hits": "n/a", "misses": n})()

    win_prob.cache_info = cache_info  # type: ignore[attr-defined]

    return win_prob


def _enumerate_draws(pile: tuple[int, ...], k: int):
    """
    Yield all tuples draw such that:
    - 0 <= draw[r] <= pile[r] for each r
    - sum(draw) == k

    Uses recursive enumeration over ranks.
    """
    n = len(pile)

    def _recurse(r: int, remaining: int, current: list[int]):
        if r == n:
            if remaining == 0:
                yield tuple(current)
            return
        lo = max(0, remaining - sum(pile[r + 1:]))
        hi = min(pile[r], remaining)
        for d in range(lo, hi + 1):
            current.append(d)
            yield from _recurse(r + 1, remaining - d, current)
            current.pop()

    yield from _recurse(0, k, [])


def initial_deal_distribution(
    params: GameParams,
) -> dict[tuple[tuple[int, ...], tuple[int, ...]], Fraction]:
    """
    Compute the probability distribution over initial (board, pile) states.

    The initial state is formed by drawing board_size cards without replacement
    from the full deck. Uses multivariate hypergeometric weighting.

    Returns a dict mapping (board_multiset, pile_multiset) -> probability.
    """
    n_ranks = params.n_ranks
    copies = params.copies_per_rank
    board_size = params.board_size

    full_deck = tuple(copies for _ in range(n_ranks))
    deck_total = n_ranks * copies  # total cards

    denom = math.comb(deck_total, board_size)

    dist: dict[tuple[tuple[int, ...], tuple[int, ...]], Fraction] = {}

    for board in _enumerate_draws(full_deck, board_size):
        # Multivariate hypergeometric numerator
        weight_num = 1
        for r in range(n_ranks):
            weight_num *= math.comb(full_deck[r], board[r])

        if weight_num == 0:
            continue

        pile = tuple(full_deck[r] - board[r] for r in range(n_ranks))
        prob = Fraction(weight_num, denom)

        key = (board, pile)
        dist[key] = dist.get(key, Fraction(0)) + prob

    # Sanity check: probabilities sum to 1
    total = sum(dist.values())
    if total != Fraction(1):
        raise ValueError(f"Initial deal distribution sums to {total}, expected 1")

    return dist


def compute_overall_win_prob(params: GameParams) -> Fraction:
    """
    Compute the exact P(win) for the given game parameters.

    Averages win_prob(board, pile) over the initial deal distribution.
    """
    win_prob = _make_win_prob(params)
    dist = initial_deal_distribution(params)

    result = Fraction(0)
    for (board, pile), prob in dist.items():
        result += prob * win_prob(board, pile)

    # Print cache stats for diagnostics
    cache_info = win_prob.cache_info()
    print(f"win_prob cache: {cache_info.currsize} states cached "
          f"({cache_info.hits} hits, {cache_info.misses} misses)")

    return result


# ---------------------------------------------------------------------------
# Monte Carlo cross-check for the scaled-down variant
# ---------------------------------------------------------------------------

def _make_deck_for_params(params: GameParams) -> list[int]:
    """
    Return a flat list of rank indices (0-based) for the full deck.
    Each rank appears copies_per_rank times.
    """
    deck = []
    for r in range(params.n_ranks):
        deck.extend([r] * params.copies_per_rank)
    return deck


def monte_carlo_win_rate(params: GameParams, n_games: int = 100_000, seed: int = 42) -> float:
    """
    Estimate P(win) for the given params via Monte Carlo simulation.

    Plays n_games random shuffles, picks the first legal move each turn.
    Returns empirical win rate.
    """
    rng = _random.Random(seed)

    pairs = params.complement_pairs
    triples = params.triple_groups
    board_size = params.board_size
    n_ranks = params.n_ranks
    base_deck = _make_deck_for_params(params)
    rank_to_complement: dict[int, int] = {}
    for (a, b) in pairs:
        rank_to_complement[a] = b
        rank_to_complement[b] = a

    wins = 0
    for _ in range(n_games):
        deck = list(base_deck)
        rng.shuffle(deck)

        # Deal board_size cards to board (as rank counts)
        board = [0] * n_ranks
        for card in deck[:board_size]:
            board[card] += 1
        pile = list(deck[board_size:])
        pile_idx = 0  # index into remaining pile

        # Play until win or stuck
        while True:
            # Check win: board empty and pile exhausted
            if sum(board) == 0 and pile_idx == len(pile):
                wins += 1
                break

            # Find first legal move
            move = None
            for (a, b) in pairs:
                if board[a] > 0 and board[b] > 0:
                    move = (a, b)
                    break
            if move is None:
                for triple in triples:
                    if all(board[r] > 0 for r in triple):
                        move = triple
                        break

            if move is None:
                # Flip logic (if enabled)
                if params.flip and pile_idx < len(pile):
                    flip_rank = pile[pile_idx]
                    pile_idx += 1
                    comp = rank_to_complement.get(flip_rank)
                    if comp is not None and board[comp] > 0:
                        # Flip succeeds: remove board complement, refill one slot
                        board[comp] -= 1
                        if pile_idx < len(pile):
                            board[pile[pile_idx]] += 1
                            pile_idx += 1
                        # Continue game
                    else:
                        break  # flip fails, lose
                else:
                    break  # stuck, no flip available, lose
                continue

            # Apply move: remove ranks from board
            k = len(move)
            for r in move:
                board[r] -= 1

            # Refill from pile
            for _ in range(k):
                if pile_idx < len(pile):
                    board[pile[pile_idx]] += 1
                    pile_idx += 1

    return wins / n_games if n_games > 0 else 0.0
