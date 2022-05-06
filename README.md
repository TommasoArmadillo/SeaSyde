# SeaSyde 🏖🏝

`SeaSyde` (**S**eries **E**xpansion **A**pproach for **SY**stem of **D**ifferential **E**quation) is a `Mathematica` package for solving the system of differential equation, associated to the Master Integrals of a given topology.

In particular, it solves the system of differential equations using a series expansion approach. This means that the solution is given as a logarithmic series. `SeaSyde` automatically performs the analitic continuation from the euclidean region, where usually the boundary conditions are imposed, to the physical region by moving in the complex plane associated to each kinematic variable. This way of performing the analytic continuation let us evaluate the master integrals with arbitrary internal complex masses in a straightforward way. 

This package is based on the work presented [here](xxxxxxxx).

## Usage 🛠⚙️
⚠️⚠️⚠️⚠️
The code is available upon request. If you are interested please contact [Tommaso Armadillo](mailto:tommaso.armadillo@uclouvain.be).
⚠️⚠️⚠️⚠️
In order to use `SeaSyde` it is sufficient to import the module in a Mathematica notebook using
``` 
  Get["/path/to/SeaSyde.m"]
```
The full documentation of the package is available in `docSeaSyde1.0.0.pdf`. Different examples can be found in the `Example/` folder. 
