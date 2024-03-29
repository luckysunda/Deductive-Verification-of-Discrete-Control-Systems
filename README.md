# Deductive-Verification-of-Discrete-Control-Systems
M. Tech. Project

We are exploring deductive approach for formal verification of discrete controllers for k-length properties. Discrete controller's verification is mainly done by model checking, one of the ways of formal verification. Model checking is simple but not easy in the aspect that if states of a system increases, it loses efficiency as its search space explodes. On the other hand, deductive approach is not so used in case of discrete controllers, but the part of learning invariant in deductive verification is already explored in detail. We want to use this advantage of deductive approach in case of discrete controllers in order to perform better than model checking in terms of efficiency.  But in the case of learning invariant, the algorithm explores all variables used in model and possibilities of invariant becomes exponential in terms of these variables. We are trying to solve this issue by providing a reduced search space in already existing state of the art learning algorithm, Horn-ICE.

Horn-ICE is taken from here: https://github.com/horn-ice/hice-dt

## Architecture
![](images/architecture.png)


## Comaprision between Horn-ICE with all the variables versus with reduced set of variables
![](images/comparision.png)
