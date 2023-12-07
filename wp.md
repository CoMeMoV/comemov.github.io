---
Title: Work Packages
---

# Work Packages

## WP0: Management and dissemination

This work package is dedicated to project management and dissemination activities including tutorials and two workshops. 

## WP1: Analysis of requirements

This work-package focuses on analysis of requirements for deductive verification of real-life industrial C code. Its results will guide the following technical work-packages. First, a set of real-world security-critical case studies will be selected, including case studies where some proof difficulties have been observed in the earlier proof attempts, and some new ones to be verified. They will be selected both from proprietary code and open-source code. Based on the selected case studies, we will create a list of representative code patterns illustrating the problems that need new memory modelling solutions and where the soundness of the verification is difficult to ensure with the currently available tools. These code patterns will be used in the technical work-packages. 

## WP2: Design of collaborative memory models

This work-package is dedicated to the global design of a sound and effective solution for addressing the issues and limitations revealed by the case studies and representative code patterns identified in WP1. The main objective is to precisely define the basic notions, memory operations and memory properties needed to specify and prove the expected properties of complex programs, and to specify the required memory models.

This design shall be precise enough to serve as a common basis for work-packages WP3 (implementation) and WP4 (formalisation). If necessary, this initial design will be further refined and improved during work-packages WP3 and WP4 in order to take into account their advances. An important part of the expected workflow is an extension of the ACSL language for region specification that will allow end users to specify complex memory properties of their programs. Its design will be another important contribution of this work-package to the project.

## WP3: Implementation

The role of this work-package is to implement the components of the new solution with the new specification and design choices defined in WP2. It includes:
- the REGION plugin responsible for memory analysis and extended ACSL annotations handling,
- the Model Dispatcher for FRAMA-C/WP, that chooses the best memory model to use according to the information provided by the REGION plugin,
- the new memory models for handling particular cases currently not well-handled by FRAMA-C/WP, notably a low-level memory model for untyped memory access and union types with heterogeneous and overlapping fields,
- the extension of the VC Generator for memory model hypotheses.

This work-package also benefits of the work done in WP4, in particular for the generation of memory  hypotheses that should be identified in WP4, as well as to check the correctness of the implementation. 

## WP4: Formalisation and correctness proofs

The proposed solution for collaborative memory models in the context of deductive verification relies on a partition of the memory into different regions, each of which is handled by a suitable memory model, efficient on the considered memory accesses. The correctness of the analysis that leads to this partitioning needs to be established. Each memory model requires the verification of side conditions, i.e. hypotheses that make the model usable and consistent. A proof that the verification of the generated side conditions indeed ensures the overall correctness of the program proof is necessary. Finally, as the goal is to combine several memory models to handle real-life industrial code, a formalisation of the collaboration and a proof of its correctness must be produced. In such formalisations and proofs, details and corner cases are particularly important and only the use of a mechanised system such as Why3 and the COQ proof assistant can guarantee they are error-free.

## WP5: Evaluation and industrial application guidelines

The first goal of this work-package is to evaluate the capacity of the solutions and tools developed in the project to perform deductive verification of large real-life products in an industrial setting. It will use technical success criteria described in the proposal. The evaluation will start with intermediate versions of tools developed in WP3 and continue with later versions as soon as new features or improvements become available. A second goal is to continuously provide feedback to the partners on the observed results and, if necessary, search together for possible improvements. Finally, the third goal is to establish a verification methodology that can be used by other industrial users.
