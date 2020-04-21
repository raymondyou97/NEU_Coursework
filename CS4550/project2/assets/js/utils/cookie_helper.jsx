import Cookies from 'js-cookie';

class CookieHelper {
    getUserSession() {
        let user_session = Cookies.get('user_session');
        if (user_session) {
            let data = JSON.parse(user_session);
            return data.data;
        }
        return false;
    }

    removeUserSession() {
        Cookies.remove('user_session');
    }
}

export default new CookieHelper();