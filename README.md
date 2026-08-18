# Rational Solids with Equal Surface Area and Volume
This repository contains computations to accompany the paper "Rational Pyramids and Prisms with Equal Surface Area and Volume" by [Kate Finnerty](https://katefinnertymath.com) and [Jacob Mayle](https://jacobmayle.com). 

This code was built on Sage 10.5 and Magma V2.29-7. It was last updated in July 2026. If you have questions or suggestions, please contact Kate Finnerty at finnerty(at)math(dot)harvard(dot)edu.

# Installation Instructions

1. If necessary, ensure you have up-to-date versions of [Magma](https://magma.maths.usyd.edu.au/magma/) and [Sage](https://www.sagemath.org/).
2. Download the repositories [MWSieveForDatabase](https://github.com/oana-adascalitei/MWSieveForDatabase) of Oana Padurariu and [QCBielliptic](https://github.com/kfinnerty19/QC_bielliptic) of Kate Finnerty.
3. From MWSieveForDatabase, move the files MWSieveCode.m and NewFunctions.m to Magma's directory folder (use the GetCurrentDirectory() command in Magma to see the current directory).
4. From QCBielliptic, move the file qc_g2_bielliptic.sage to Sage's directory folder (to see the current directory in Sage, run import os followed by os.getcwd()).
5. Follow the steps described in MainCode.m in this repository to replicate the analysis.

# Description of Files
- MainCode.m is the primary file of the repository and begins with instructions to replicate the analysis. It also contains all relevant files to run the sieve. Note that this must be run in multiple parts. Magma output is required for the quadratic Chabauty computations in Sage, and the Sage output is in turn required for the final sieving computation in Magma. 
- SieveOutput.txt contains the printed output from the final step of MainCode.m so that one can inspect the output without running the full computation, if one wishes.
- QuadraticChabautyAnalysis.sage contains three calls to the functionality of qc_g2_bielliptic.sage, running quadratic Chabauty for three different primes.