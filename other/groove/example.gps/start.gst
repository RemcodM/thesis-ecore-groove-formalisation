<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="start">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>167 8 112 51</string>
            </attr>
        </node>
        <node id="n1">
            <attr name="layout">
                <string>166 205 112 51</string>
            </attr>
        </node>
        <node id="n2">
            <attr name="layout">
                <string>9 126 183 17</string>
            </attr>
        </node>
        <node id="n3">
            <attr name="layout">
                <string>403 16 114 34</string>
            </attr>
        </node>
        <node id="n4">
            <attr name="layout">
                <string>400 120 117 34</string>
            </attr>
        </node>
        <node id="n5">
            <attr name="layout">
                <string>394 216 130 34</string>
            </attr>
        </node>
        <node id="n6">
            <attr name="layout">
                <string>624 121 147 34</string>
            </attr>
        </node>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>id:Renter1</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>type:Renter</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>let:age = 24</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>let:name = "J.A."</string>
            </attr>
        </edge>
        <edge from="n0" to="n2">
            <attr name="label">
                <string>payment_interval</string>
            </attr>
        </edge>
        <edge from="n0" to="n3">
            <attr name="label">
                <string>rents</string>
            </attr>
        </edge>
        <edge from="n0" to="n4">
            <attr name="label">
                <string>rents</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>id:Renter2</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>type:Renter</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>let:age = 23</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>let:name = "M.S."</string>
            </attr>
        </edge>
        <edge from="n1" to="n2">
            <attr name="label">
                <string>payment_interval</string>
            </attr>
        </edge>
        <edge from="n1" to="n5">
            <attr name="label">
                <string>rents</string>
            </attr>
        </edge>
        <edge from="n2" to="n2">
            <attr name="label">
                <string>type:PaymentInterval$MONTH</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>id:Longhorn</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n3" to="n3">
            <attr name="label">
                <string>let:number = 1</string>
            </attr>
        </edge>
        <edge from="n3" to="n0">
            <attr name="label">
                <string>renter</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>id:Shorthorn</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>let:number = 2</string>
            </attr>
        </edge>
        <edge from="n4" to="n0">
            <attr name="label">
                <string>renter</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>id:onghornLay</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>let:number = 3</string>
            </attr>
        </edge>
        <edge from="n5" to="n1">
            <attr name="label">
                <string>renter</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>id:TwoRem</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>type:House</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>let:name = "Small House"</string>
            </attr>
        </edge>
        <edge from="n6" to="n5">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n6" to="n4">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n6" to="n3">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
    </graph>
</gxl>
