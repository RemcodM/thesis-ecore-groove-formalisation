<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="step3">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>70 16 97 17</string>
            </attr>
        </node>
        <node id="n1">
            <attr name="layout">
                <string>192 61 67 17</string>
            </attr>
        </node>
        <node id="n2">
            <attr name="layout">
                <string>399 71 67 17</string>
            </attr>
        </node>
        <node id="n3">
            <attr name="layout">
                <string>274 16 97 17</string>
            </attr>
        </node>
        <node id="n4">
            <attr name="layout">
                <string>63 115 111 17</string>
            </attr>
        </node>
        <node id="n5">
            <attr name="layout">
                <string>267 115 111 17</string>
            </attr>
        </node>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>id:Jane</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>type:Contact</string>
            </attr>
        </edge>
        <edge from="n0" to="n1">
            <attr name="label">
                <string>name</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>string:"Jane Doe"</string>
            </attr>
        </edge>
        <edge from="n2" to="n2">
            <attr name="label">
                <string>string:"John Doe"</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>id:John</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>type:Contact</string>
            </attr>
        </edge>
        <edge from="n3" to="n2">
            <attr name="label">
                <string>name</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>id:Addr1</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>type:Address</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>id:Addr2</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>type:Address</string>
            </attr>
        </edge>
    </graph>
</gxl>
