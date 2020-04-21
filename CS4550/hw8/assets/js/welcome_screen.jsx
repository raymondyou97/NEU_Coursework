import React from 'react';
import _ from 'lodash';
import { connect } from 'react-redux';

export default connect((state) => (state)) ((props) => {
    if(props.session.token && props.session.email) {
        return <h3>Welcome to Task Tracker SPA!</h3>
    } else {
        return <h3>Please register or login!</h3>
    }
})