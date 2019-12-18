<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="invalid7">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>79 138 42 17</string>
            </attr>
        </node>
        <node id="n1">
            <attr name="layout">
                <string>79 35 46 17</string>
            </attr>
        </node>
        <node id="n2">
            <attr name="layout">
                <string>160 89 89 17</string>
            </attr>
        </node>
        <node id="n3">
            <attr name="layout">
                <string>206 182 8 17</string>
            </attr>
        </node>
        <node id="n4">
            <attr name="layout">
                <string>274 34 39 17</string>
            </attr>
        </node>
        <node id="n5">
            <attr name="layout">
                <string>267 85 127 17</string>
            </attr>
        </node>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n0" to="n3">
            <attr name="label">
                <string>number</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>type:House</string>
            </attr>
        </edge>
        <edge from="n1" to="n2">
            <attr name="label">
                <string>name</string>
            </attr>
        </edge>
        <edge from="n1" to="n0">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n2" to="n2">
            <attr name="label">
                <string>string:"Other house"</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>int:1</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>type:Hotel</string>
            </attr>
        </edge>
        <edge from="n4" to="n5">
            <attr name="label">
                <string>name</string>
            </attr>
        </edge>
        <edge from="n4" to="n0">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>string:"Some fancy Hotel"</string>
            </attr>
        </edge>
    </graph>
</gxl>
