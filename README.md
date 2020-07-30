# Alloy Diff 

This is the repository for the paper:

[Jan Oliver Ringert](https://ringert.blogspot.com) and Syed Wali Waqee: _Semantic Comparisons of Alloy Models_. To appear in MoDELS 2020.

* An author's [preprint of the paper is available here](docs/Semantic_Comparisons_of_Alloy_Models.pdf)
* See a small demo and an overview of the artifacts: https://youtu.be/JA93sy2oHfo 
* See out artifact submission: [docs/artefact_overview.pdf](docs/artefact_overview.pdf)

More information on Alloy can be found at: http://alloytools.org/documentation.html.

## Added Projects

We have started out from the [https://github.com/AlloyTools/org.alloytools.alloy](AlloyTools repository) and added various projects with our implementation, evaluation data, and experiments code as detailed below.

## New Alloy Diff Projects

* [org.alloytools.alloy.diff](org.alloytools.alloy.diff) – The main implementation of merging Alloy models and for generating semantic comparison commands

## Modified Alloy Projects

* [org.alloytools.alloy.application](org.alloytools.alloy.application) – The integration of our GUI extension for semantic comparisons of Alloy models
* All other projects are described in Alloy's original [README](README_original.md)

## Dataset Projects

These projects include datasets from other paper that we have used for evaluation.

* [experiments](experiments) – scripts, binaries, and resulting CSVs from our experiments
* [iAlloy-dataset-master](iAlloy-dataset-master) – From [https://github.com/wenxiwang/iAlloy-dataset](https://github.com/wenxiwang/iAlloy-dataset)
* [platinum-experiment-data](platinum-experiment-data) – From [https://sites.google.com/view/platinum-repository](https://sites.google.com/view/platinum-repository)
* [models-master](models-master) – From [https://github.com/AlloyTools/models](https://github.com/AlloyTools/models)


## Additional (Experimental) Projects

These projects are not needed for the semantic comparison of Alloy models.

* [org.alloytools.alloy.instcheck](org.alloytools.alloy.instcheck) – An implementation to enumerate Alloy instances and check their validity in another Alloy model (this is used for validation)
* [org.alloytools.alloy.flatten](org.alloytools.alloy.flatten) – Incomplete attempt to flatten inheritance and other language features in Alloy models (this could have lead to a multi-step transformation where each step is small and can be validated more easily)



## 