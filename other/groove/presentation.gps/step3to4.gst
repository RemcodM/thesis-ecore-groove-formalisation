<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="step3to4">
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
        <node id="n6">
            <attr name="layout">
                <string>21 179 95 17</string>
            </attr>
        </node>
        <node id="n7">
            <attr name="layout">
                <string>260 177 100 17</string>
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
        <edge from="n4" to="n6">
            <attr name="label">
                <string>line</string>
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
        <edge from="n5" to="n7">
            <attr name="label">
                <string>line</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>string:"Some Str. 55"</string>
            </attr>
        </edge>
        <edge from="n7" to="n7">
            <attr name="label">
                <string>string:"Another Str. 1"</string>
            </attr>
        </edge>
    </graph>
</gxl>
