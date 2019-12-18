<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="contact2">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>106 142 57 34</string>
            </attr>
        </node>
        <node id="n2">
            <attr name="layout">
                <string>99 290 61 17</string>
            </attr>
        </node>
        <node id="n4">
            <attr name="layout">
                <string>227 345 120 17</string>
            </attr>
        </node>
        <node id="n5">
            <attr name="layout">
                <string>112 380 27 17</string>
            </attr>
        </node>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>id:Example</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>type:Contact</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>flag:fav</string>
            </attr>
        </edge>
        <edge from="n0" to="n2">
            <attr name="label">
                <string>addresses</string>
            </attr>
        </edge>
        <edge from="n2" to="n2">
            <attr name="label">
                <string>type:Address</string>
            </attr>
        </edge>
        <edge from="n2" to="n5">
            <attr name="label">
                <string>country</string>
            </attr>
        </edge>
        <edge from="n2" to="n4">
            <attr name="label">
                <string>addressLine</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>string:"University Str. 15"</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>string:"NL"</string>
            </attr>
        </edge>
    </graph>
</gxl>
