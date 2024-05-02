# Current stable version: 1.1.1 - 🏖🏝 Public Release

## Version 1.1.1 - 2024/05/02 - ❌🐞 Error estimate and bug correction
- Added an error estimate on the result. This is obtained by considering the difference between the complete solution and and solution without its last 3 terms, both evaluated at half the radius of convergence.
- Corrected some bugs related to the loss of numerical precision while solving the system on top of singularities.
- Corrected a bug in `DetermineAsymptoticBoundaryConditions`.

## Version 1.1.0 - 2022/09/14 - 👫📚 Coupled system
- `SeaSyde` can now solve system of coupled differential equations and it is not anymore limited to systems in upper-triangular form.
- General optimization of the workflow.
- Added a check for insufficient numerical precision. If so, the package automatically increases it.
- Improved the choice of the path when the starting and ending point are to the right of singularities.

## Version 1.0.0 - 2022/05/06 - 🏖🏝 Public Release
Public release of the code. For a full review of the package please see [arXiv](https://arxiv.org/abs/2205.03345). The documentation can be found [here](https://github.com/TommasoArmadillo/SeaSyde/blob/main/docSeaSyde1.0.0.pdf).
