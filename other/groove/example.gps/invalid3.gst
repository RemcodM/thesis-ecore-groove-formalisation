<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="invalid3">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>57 150 95 34</string>
            </attr>
        </node>
        <node id="n1">
            <attr name="layout">
                <string>29 27 145 34</string>
            </attr>
        </node>
        <node id="n2">
            <attr name="layout">
                <string>275 83 19 19</string>
            </attr>
        </node>
        <node id="n3">
            <attr name="layout">
                <string>216 216 19 19</string>
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
                <string>bool:true</string>
            </attr>
        </edge>
    </graph>
</gxl>
