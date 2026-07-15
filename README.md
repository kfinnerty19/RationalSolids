# Rational Pyramids and Prisms with Equal Surface Area and Volume
This repository contains computations to accompany the forthcoming paper "Rational Pyramids and Prisms with Equal Surface Area and Volume" by [Kate Finnerty](katefinnertymath.com) and [Jacob Mayle](jacobmayle.com). 


This code was built on Sage 10.5 and Magma V2.29-7. It was last updated in July 2026. If you have questions or suggestions, please contact Kate Finnerty at finnerty(at)math(dot)harvard(dot)edu.

# Description of Files
- MWSieveCode.m contains code of [Steffen Mueller](https://github.com/steffenmueller/), written to accompany work on quadratic Chabauty for modular curves. It defines the core functions of the Mordell-Weil sieve.
- MainCode.m is the primary file of the repository and begins with instructions to replicate the analysis. It also contains all relevant files to run the sieve. Note that this must be run in multiple parts. Magma output is required for the quadratic Chabauty computations in Sage, and the Sage output is in turn required for the final sieving computation in Magma. For more details, see the instructions at the top of this file.
- NewFunctions.m contains functions to assist in the Mordell-Weil sieve for the specific case of bielliptic curves. This is code of [Oana Padurariu](https://sites.google.com/view/oanapadurariu/home) [\[4\]](#References) to accompany the work of Bianchi--Padurariu [\[1\]](#References).
- SieveOutput.txt contains the printed output from the final step of MainCode.m so that one can inspect the output without running the full computation, if one wishes.
- qc_g2_bielliptic.sage defines functionality to perform quadratic Chabauty on any genus 2 bielliptic curve given by an equation of the form `y^2 = a_6*x^6 + a_4*x^4 + a_2*x^2 + a_0`, with `a_i\in \ZZ`, such that the corresponding elliptic curves each have rank 1 and using a prime of good reduction. This code is from Kate Finnerty's project [Quadratic Chabauty Experiments on Genus 2 Bielliptic Modular Curves in the LMFDB] [\[2\]](#References), which in turn was built on [Francesca Bianchi's](https://sites.google.com/view/francescabianchi) SageMath code. Bianchi's code is discussed in the paper ["Rational points on rank 2 genus 2 bielliptic curves in the LMFDB"](https://arxiv.org/abs/2212.11635) by Bianchi and Padurariu [\[1\]](#References).
- ratptscalc.sage contains three calls to the functionality of qc_g2_bielliptic.sage, running quadratic Chabauty for three different primes. In our particular example, the output for two quadratic Chabauty primes is sufficient, as discussed in the paper, but this is not the case for all bielliptic curves.

# References
1. F. Bianchi and O. Padurariu. "Rational Points on Rank 2 Genus 2 Bielliptic Curves in the LMFDB. _LuCaNT: LMFDB, Computation, and Number Theory_. 2024. 
2. K. Finnerty. "Quadratic Chabauty Experiments on Genus 2 Bielliptic Modular Curves in the LMFDB."  _LuCaNT: LMFDB, Computation, and Number Theory_. 2026.
3. J.S. Mueller, "QCMod." [Github repository.](https://github.com/steffenmueller/QCMod)
4. O. Padurariu. "MWSieveForDatabase." [Github repository.](https://github.com/oana-adascalitei/MWSieveForDatabase)
