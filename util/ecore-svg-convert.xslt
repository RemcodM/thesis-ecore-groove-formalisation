<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:svg="http://www.w3.org/2000/svg">

<xsl:output indent="yes"/>
<xsl:strip-space elements="*"/>

<xsl:template match="node()|@*">
    <xsl:copy>
        <xsl:apply-templates select="node()|@*"/>
    </xsl:copy>
</xsl:template>

<xsl:template match="@font-family">
  <xsl:attribute name="font-family">Ubuntu</xsl:attribute>
</xsl:template>

<xsl:template match="@font-size">
  <xsl:attribute name="font-size">10</xsl:attribute>
</xsl:template>

<xsl:template match="svg:text/@y">
  <xsl:attribute name="y">
    <xsl:value-of select="current()-6" />
  </xsl:attribute>
</xsl:template>

</xsl:stylesheet>
