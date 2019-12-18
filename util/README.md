## Utilities

This directory contains some utilities used in creating this repository and its contents.

- `ecore-svg-convert` and `ecore-svg-convert.xslt`: Shell script for converting SVG files of Ecore models generated with Eclipse to PDF. Because of a bug in Eclipse at the time of writing, the font sizes generated for the SVG are too large. An XML transformation is used to reduce the font sizes before converting it to PDF. [Inkscape](https://inkscape.org/ "Inkscape's homepage") is used for the conversion to PDF. `xsltproc` is used to perform the XML transformation.
- `pages_generator.sh`: Simple BASH script that generates the references to the Isabelle proofs in markdown format.
