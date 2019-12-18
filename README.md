# A formalisation of EMF by expressing Ecore as GROOVE graphs

This is the repository belonging to master thesis 'A formalisation of EMF by expressing Ecore as GROOVE graphs'. It contains the source files of the thesis itself, the corresponding Isabelle proofs as well as other related files.

## Abstract

Within the field of software verification, software is verified to be correct using models. However, the modelling landscape is very diverse, and multiple modelling techniques exist to model software. Model transformations can help to bridge the gap between these techniques, but often do not have a formal foundation, which is problematic for software verification. Within this work, the model transformations between models based on EMF's Ecore and GROOVE grammars are formalised. A transformation framework is introduced to create model transformations between Ecore models and GROOVE grammars while maintaining a formal foundation. This framework allows for creating significant model transformations out of smaller transformations that are more easy to proof. An application is used to show how model transformations can be built using this framework.

## Cite

When using BibTeX or BibLaTeX, you can cite the work as follows:
```
@misc{deman-2019,
    month = {December},
    title = {A formalisation of {EMF} by expressing {Ecore} as {GROOVE} graphs},
    author = {R.J.P. de {Man}},
    year = {2019},
    url = {http://purl.utwente.nl/essays/80247},
    abstract = {Within the field of software verification, software is verified to be correct using models. However, the modelling landscape is very diverse, and multiple modelling techniques exist to model software. Model transformations can help to bridge the gap between these techniques, but often do not have a formal foundation, which is problematic for software verification. Within this work, the model transformations between models based on EMF's Ecore and GROOVE grammars are formalised. A transformation framework is introduced to create model transformations between Ecore models and GROOVE grammars while maintaining a formal foundation. This framework allows for creating significant model transformations out of smaller transformations that are more easy to proof. An application is used to show how model transformations can be built using this framework.}
}
```

For other means for citing this work, please refer to http://purl.utwente.nl/essays/80247.

## License

The code within this repository is published under the Academic Free License 3.0. Refer to the `LICENSE` file within this repository for more information.

## Layout

- `isabelle/`: Contains all [Isabelle](https://isabelle.in.tum.de/ "Isabelle's homepage") proofs.
- `other/`: Contains other files related to this thesis.
- `presentation/`: Contains the source files of the presentation corresponding to this thesis.
- `thesis/`: Contains the source files of the thesis itself.
- `util/`: Some utilities used to build this repository and its contents.
- `thesis.pdf`: A PDFLaTeX compiled version of the thesis.
