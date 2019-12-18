<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<gxl xmlns="http://www.gupro.de/GXL/gxl-1.0.dtd">
    <graph role="graph" edgeids="false" edgemode="directed" id="step08">
        <attr name="$version">
            <string>curly</string>
        </attr>
        <node id="n0">
            <attr name="layout">
                <string>215 619 134 34</string>
            </attr>
        </node>
        <node id="n1">
            <attr name="layout">
                <string>206 16 119 34</string>
            </attr>
        </node>
        <node id="n4">
            <attr name="layout">
                <string>212 406 145 34</string>
            </attr>
        </node>
        <node id="n5">
            <attr name="layout">
                <string>360 40 161 34</string>
            </attr>
        </node>
        <node id="n6">
            <attr name="layout">
                <string>26 38 146 34</string>
            </attr>
        </node>
        <node id="n7">
            <attr name="layout">
                <string>123 129 117 34</string>
            </attr>
        </node>
        <node id="n8">
            <attr name="layout">
                <string>282 130 117 34</string>
            </attr>
        </node>
        <node id="n9">
            <attr name="layout">
                <string>123 239 115 17</string>
            </attr>
        </node>
        <node id="n10">
            <attr name="layout">
                <string>283 239 115 17</string>
            </attr>
        </node>
        <node id="n11">
            <attr name="layout">
                <string>37 420 115 17</string>
            </attr>
        </node>
        <node id="n12">
            <attr name="layout">
                <string>416 414 115 17</string>
            </attr>
        </node>
        <node id="n13">
            <attr name="layout">
                <string>425 319 115 17</string>
            </attr>
        </node>
        <node id="n14">
            <attr name="layout">
                <string>27 505 128 34</string>
            </attr>
        </node>
        <node id="n15">
            <attr name="layout">
                <string>223 504 128 34</string>
            </attr>
        </node>
        <node id="n16">
            <attr name="layout">
                <string>417 505 128 34</string>
            </attr>
        </node>
        <node id="n17">
            <attr name="layout">
                <string>102 628 19 19</string>
            </attr>
        </node>
        <node id="n19">
            <attr name="layout">
                <string>253 104 19 19</string>
            </attr>
        </node>
        <node id="n21">
            <attr name="layout">
                <string>11 125 19 19</string>
            </attr>
        </node>
        <node id="n22">
            <attr name="layout">
                <string>498 136 19 19</string>
            </attr>
        </node>
        <node id="n23">
            <attr name="layout">
                <string>73 592 19 19</string>
            </attr>
        </node>
        <node id="n24">
            <attr name="layout">
                <string>208 568 19 19</string>
            </attr>
        </node>
        <node id="n25">
            <attr name="layout">
                <string>506 580 19 19</string>
            </attr>
        </node>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>id:BHP</string>
            </attr>
        </edge>
        <edge from="n0" to="n0">
            <attr name="label">
                <string>type:House</string>
            </attr>
        </edge>
        <edge from="n0" to="n15">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n0" to="n17">
            <attr name="label">
                <string>name</string>
            </attr>
        </edge>
        <edge from="n0" to="n16">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n0" to="n14">
            <attr name="label">
                <string>rooms</string>
            </attr>
            <attr name="layout">
                <string>484 0 248 616 125 543 11</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>id:TR</string>
            </attr>
        </edge>
        <edge from="n1" to="n1">
            <attr name="label">
                <string>type:House</string>
            </attr>
        </edge>
        <edge from="n1" to="n19">
            <attr name="label">
                <string>name</string>
            </attr>
        </edge>
        <edge from="n1" to="n7">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n1" to="n8">
            <attr name="label">
                <string>rooms</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>id:SmallSize</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>type:RoomSize</string>
            </attr>
        </edge>
        <edge from="n4" to="n4">
            <attr name="label">
                <string>flag:SMALL</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>id:MediumSize</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>type:RoomSize</string>
            </attr>
        </edge>
        <edge from="n5" to="n5">
            <attr name="label">
                <string>flag:MEDIUM</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>id:LargeSize</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>type:RoomSize</string>
            </attr>
        </edge>
        <edge from="n6" to="n6">
            <attr name="label">
                <string>flag:LARGE</string>
            </attr>
        </edge>
        <edge from="n7" to="n7">
            <attr name="label">
                <string>id:TRRoom1</string>
            </attr>
        </edge>
        <edge from="n7" to="n7">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n7" to="n6">
            <attr name="label">
                <string>room_size</string>
            </attr>
        </edge>
        <edge from="n7" to="n21">
            <attr name="label">
                <string>room_id</string>
            </attr>
        </edge>
        <edge from="n8" to="n8">
            <attr name="label">
                <string>id:TRRoom2</string>
            </attr>
        </edge>
        <edge from="n8" to="n8">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n8" to="n22">
            <attr name="label">
                <string>room_id</string>
            </attr>
        </edge>
        <edge from="n8" to="n5">
            <attr name="label">
                <string>room_size</string>
            </attr>
        </edge>
        <edge from="n9" to="n9">
            <attr name="label">
                <string>id:Tenant1</string>
            </attr>
        </edge>
        <edge from="n9" to="n9">
            <attr name="label">
                <string>type:Tenant</string>
            </attr>
        </edge>
        <edge from="n10" to="n10">
            <attr name="label">
                <string>id:Tenant2</string>
            </attr>
        </edge>
        <edge from="n10" to="n10">
            <attr name="label">
                <string>type:Tenant</string>
            </attr>
        </edge>
        <edge from="n11" to="n11">
            <attr name="label">
                <string>id:Tenant3</string>
            </attr>
        </edge>
        <edge from="n11" to="n11">
            <attr name="label">
                <string>type:Tenant</string>
            </attr>
        </edge>
        <edge from="n12" to="n12">
            <attr name="label">
                <string>id:Tenant4</string>
            </attr>
        </edge>
        <edge from="n12" to="n12">
            <attr name="label">
                <string>type:Tenant</string>
            </attr>
        </edge>
        <edge from="n13" to="n13">
            <attr name="label">
                <string>id:Tenant5</string>
            </attr>
        </edge>
        <edge from="n13" to="n13">
            <attr name="label">
                <string>type:Tenant</string>
            </attr>
        </edge>
        <edge from="n14" to="n14">
            <attr name="label">
                <string>id:BHPRoomA</string>
            </attr>
        </edge>
        <edge from="n14" to="n14">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n14" to="n23">
            <attr name="label">
                <string>room_id</string>
            </attr>
        </edge>
        <edge from="n14" to="n4">
            <attr name="label">
                <string>room_size</string>
            </attr>
        </edge>
        <edge from="n15" to="n15">
            <attr name="label">
                <string>id:BHPRoomB</string>
            </attr>
        </edge>
        <edge from="n15" to="n15">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n15" to="n4">
            <attr name="label">
                <string>room_size</string>
            </attr>
        </edge>
        <edge from="n15" to="n24">
            <attr name="label">
                <string>room_id</string>
            </attr>
        </edge>
        <edge from="n16" to="n16">
            <attr name="label">
                <string>id:BHPRoomC</string>
            </attr>
        </edge>
        <edge from="n16" to="n16">
            <attr name="label">
                <string>type:Room</string>
            </attr>
        </edge>
        <edge from="n16" to="n25">
            <attr name="label">
                <string>room_id</string>
            </attr>
        </edge>
        <edge from="n16" to="n4">
            <attr name="label">
                <string>room_size</string>
            </attr>
        </edge>
        <edge from="n17" to="n17">
            <attr name="label">
                <string>string:"B.H. Paleis"</string>
            </attr>
        </edge>
        <edge from="n19" to="n19">
            <attr name="label">
                <string>string:"TwoRem"</string>
            </attr>
        </edge>
        <edge from="n21" to="n21">
            <attr name="label">
                <string>string:"1"</string>
            </attr>
        </edge>
        <edge from="n22" to="n22">
            <attr name="label">
                <string>string:"2"</string>
            </attr>
        </edge>
        <edge from="n23" to="n23">
            <attr name="label">
                <string>string:"A"</string>
            </attr>
        </edge>
        <edge from="n24" to="n24">
            <attr name="label">
                <string>string:"B"</string>
            </attr>
        </edge>
        <edge from="n25" to="n25">
            <attr name="label">
                <string>string:"C"</string>
            </attr>
        </edge>
    </graph>
</gxl>
