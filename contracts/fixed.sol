contract SmartAR {
    function add_uint256(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        assert(c >= a);
        return c;
    }
    function sub_uint256(uint256 a, uint256 b) internal pure returns (uint256) {
        assert(b <= a);
        return a - b;
    }
}
pragma solidity ^0.4.10;

contract BuggyContract is SmartAR {
    uint public x;
    uint public y;
    uint public z;

    function BuggyFunction_19_min3(uint a, uint b, uint c, uint d) public {
        if (a > b) {
            x = sub_uint256(d, a);  // bug
            if (b > c) {
                y = d - b;  // bug
                z = d - c;  // bug
            } else {
                y = d - b;  // bug
                x = sub_uint256(d, c);  // bug
            }
        } else {
            x = sub_uint256(d, b);  // bug
            y = d - a;  // bug
        }
    }

    function BuggyFunction_20_min3(uint a, uint b, uint c, uint d) public {
        if (a > b) {
            x = a + b;  // bug
            if (b > c) {
                y = a + b;  // bug
            } else {
                z = a + b;  // bug
            }
        } else {
            x = add_uint256(b, c);  // bug
            y = a + c;  // bug
        }
        z = add_uint256(a, b);  // bug
    }

}
