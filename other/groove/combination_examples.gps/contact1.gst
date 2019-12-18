<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="contact1">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>158 304 221 51</string>
            </attr>
        </node>
        <node id="n1">
            <attr name="layout">
                <string>421 176 19 19</string>
            </attr>
        </node>
        <node id="n3">
            <attr name="layout">
                <string>318 242 19 19</string>
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
        <edge from="n0" to="n1">
            <attr name="label">
                <string>firstName</string>
            </attr>
        </edge>
        <edge from="n0" to="n3">
            <attr name="label">
                <string>email</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>string:"Netwerkprofessort"</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>string:"networks@example.com"</string>
            </attr>
        </edge>
    </graph>
</gxl>
