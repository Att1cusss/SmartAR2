pragma solidity ^0.4.10;

contract BuggyContract {
    uint public x;
    uint public y;
    uint public z;

    function BuggyFunction_19_min3(uint a, uint b, uint c, uint d) public {
        if (a > b) {
            x = d - a;  // bug
            if (b > c) {
                y = d - b;  // bug
                z = d - c;  // bug
            } else {
                y = d - b;  // bug
                x = d - c;  // bug
            }
        } else {
            x = d - b;  // bug
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
            x = b + c;  // bug
            y = a + c;  // bug
        }
        z = a + b;  // bug
    }

}
