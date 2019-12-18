<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="step4to5">
        <attr name="$version">
            <string>curly</string>
        </attr>
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
        <node id="n8">
            <attr name="layout">
                <string>184 205 59 17</string>
            </attr>
        </node>
        <node id="n9">
            <attr name="layout">
                <string>421 195 59 17</string>
            </attr>
        </node>
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
        <edge from="n4" to="n8">
            <attr name="label">
                <string>postcode</string>
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
        <edge from="n5" to="n9">
            <attr name="label">
                <string>postcode</string>
            </attr>
        </edge>
        <edge from="n8" to="n8">
            <attr name="label">
                <string>string:"4084LH"</string>
            </attr>
        </edge>
        <edge from="n9" to="n9">
            <attr name="label">
                <string>string:"4088LH"</string>
            </attr>
        </edge>
    </graph>
</gxl>
